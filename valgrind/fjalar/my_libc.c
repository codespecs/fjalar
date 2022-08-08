/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* Replacement implementations of libc-like functions that
   aren't provided in Valgrind's core. */

/* Most of this code has been borrowed from dietlibc, by Felix von
   Leitner <felix-dietlibc@fefe.de> et al., and is licensed under the
   GPL. */

#include "my_libc.h"

#include "pub_tool_basics.h"
#include "pub_tool_vki.h"  // needed by pub_tool_libcfile.h
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_mallocfree.h"

#include <limits.h>

extern char* fptostr (double x, int width, int preci, char mode, char* buf, int maxlen);
void setNOBUF(FILE *stream);

/* ctype.h */

int isalnum(int ch) {
  return (unsigned int)((ch | 0x20) - 'a') < 26u  ||
         (unsigned int)( ch         - '0') < 10u;
}

int isalpha(int c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}

int isdigit(int c) {
    return c >= '0' && c <= '9';
}

int isspace ( int ch )
{
    return (unsigned int)(ch - 9) < 5u  ||  ch == ' ';
}

int isxdigit ( int ch )
{
    return (unsigned int)( ch         - '0') < 10u  ||
           (unsigned int)((ch | 0x20) - 'a') <  6u;
}


/* errno.h */
int errno;

/* stdio.h */

#define BUFSIZE 4194304  // 0x400000

struct __stdio_file {
  int fd;
  int flags;
  UInt bs;  /* read: bytes in buffer */
  UInt bm;  /* position in buffer */
  UInt buflen;      /* length of buf */
  char *buf;
  struct __stdio_file *next;    /* for fflush */
  vki_pid_t popen_kludge;
  unsigned char ungetbuf;
  char ungotten;
};

static FILE *__stdio_root;

#define ERRORINDICATOR 1
#define EOFINDICATOR 2
#define BUFINPUT 4
#define BUFLINEWISE 8
#define NOBUF 16
#define STATICBUF 32
#define FDPIPE 64
#define CANREAD 128
#define CANWRITE 256

static char __stdin_buf[BUFSIZE];
static FILE __stdin = {
  .fd=0,
  .flags=BUFINPUT|BUFLINEWISE|STATICBUF|CANREAD,
  .bs=0, .bm=0,
  .buflen=BUFSIZE,
  .buf=__stdin_buf,
  .next=0,
  .popen_kludge=0,
  .ungetbuf=0,
  .ungotten=0,
};

FILE *stdin=&__stdin;

static char __stdout_buf[BUFSIZE];
static FILE __stdout = {
  .fd=1,
  .flags=BUFLINEWISE|STATICBUF|CANWRITE,
  .bs=0, .bm=0,
  .buflen=BUFSIZE,
  .buf=__stdout_buf,
  .next=0,
  .popen_kludge=0,
  .ungetbuf=0,
  .ungotten=0,
};

FILE *stdout=&__stdout;

static FILE __stderr = {
  .fd=2,
  .flags=NOBUF|CANWRITE,
  .bs=0, .bm=0,
  .buflen=0,
  .buf=0,
  .next=0,
  .popen_kludge=0,
  .ungetbuf=0,
  .ungotten=0,
};

FILE *stderr=&__stderr;

void setNOBUF(FILE *stream) {
    stream->flags |= NOBUF;
}    

static int __stdio_parse_mode(const char *mode) {
  int f=0;
  for (;;) {
    switch (*mode) {
    case 0: return f;
    case 'b': break;
    case 'r': f=VKI_O_RDONLY; break;
    case 'w': f=VKI_O_WRONLY|VKI_O_CREAT|VKI_O_TRUNC; break;
    case 'a': f=VKI_O_WRONLY|VKI_O_CREAT|VKI_O_APPEND; break;
    case '+': f=(f&(~VKI_O_WRONLY))|VKI_O_RDWR; break;
    }
    ++mode;
  }
}

static FILE*__stdio_init_file(int fd,int closeonerror,int mode) {
    FILE *tmp=(FILE*)VG_(malloc)("my_libc.c: stdio_init_file.1", sizeof(FILE));
  if (!tmp) goto err_out;
  tmp->buf=(char*)VG_(malloc)("my_libc.c: stdio_init_file.2", BUFSIZE);
  if (!tmp->buf) {
    VG_(free)(tmp);
err_out:
    if (closeonerror) VG_(close)(fd);
    errno=VKI_ENOMEM;
    return 0;
  }
  tmp->fd=fd;
  tmp->bm=0;
  tmp->bs=0;
  tmp->buflen=BUFSIZE;
  {
    struct vg_stat st;
    VG_(fstat)(fd,&st);
    tmp->flags=(VKI_S_ISFIFO(st.mode))?FDPIPE:0;
  }
  switch (mode&3) {
  case VKI_O_RDWR: tmp->flags|=CANWRITE;
                   /* Fall through.  */
  case VKI_O_RDONLY: tmp->flags|=CANREAD; break;
  case VKI_O_WRONLY: tmp->flags|=CANWRITE;
  }
  tmp->popen_kludge=0;
  tmp->next=__stdio_root;
  __stdio_root=tmp;
  tmp->ungotten=0;
  return tmp;
}

FILE *fopen(const char *path, const char *mode) {
  int f=0;      /* O_RDONLY, O_WRONLY or O_RDWR */
  int fd;
  SysRes sr;

  f=__stdio_parse_mode(mode);
  f |= VKI_O_LARGEFILE;
  sr = VG_(open)(path, f, 0666);
  if (sr_isError(sr)) {
    errno = sr_Err(sr);
    return 0;
  }
  fd = sr_Res(sr);
  return __stdio_init_file(fd,1,f);
}

FILE *fdopen(int filedes, const char *mode) {
  int f=0;      /* O_RDONLY, O_WRONLY or O_RDWR */

  f=__stdio_parse_mode(mode);
  if (filedes<0) { errno=VKI_EBADF; return 0; }
  return __stdio_init_file(filedes,0,f);
}


int fflush(FILE *stream) {
  if (stream->flags&BUFINPUT) {
    register int tmp;
    if ((tmp=stream->bm-stream->bs)) {
    VG_(lseek)(stream->fd,tmp,VKI_SEEK_CUR);
    }
    stream->bs=stream->bm=0;
  } else if (stream->bm) {
    int ret = VG_(write)(stream->fd,stream->buf,stream->bm);
    if (ret == -1 || (UInt)ret != stream->bm) {
      stream->flags|=ERRORINDICATOR;
      return -1;
    }
    stream->bm=0;
  }
  return 0;
}

int fclose(FILE *stream) {
  int res;
  FILE *f,*fl;
  res=fflush(stream);
  VG_(close)(stream->fd);
  for (fl=0,f=__stdio_root; f; fl=f,f=f->next)
    if (f==stream) {
      if (fl)
        fl->next=f->next;
      else
        __stdio_root=f->next;
      break;
    }
  if ((!(stream->flags&STATICBUF))&&(stream->buf))
    VG_(free)(stream->buf);
  VG_(free)(stream);
  return res;
}


int feof(FILE*stream) {
  /* yuck!!! */
  if (stream->ungotten) return 0;
  return (stream->flags&EOFINDICATOR);
}

int ferror(FILE*stream) {
  return (stream->flags&ERRORINDICATOR);
}

static int __fflush4(FILE *stream,int next) {
  if ((stream->flags&BUFINPUT)!=next) {
    int res=fflush(stream);
    stream->flags=(stream->flags&~BUFINPUT)|next;
    return res;
  }
  return 0;
}


int fgetc(FILE *stream) {
  unsigned char c;
  if (!(stream->flags&CANREAD)) goto kaputt;
  if (stream->ungotten) {
    stream->ungotten=0;
    return stream->ungetbuf;
  }
  if (feof(stream))
    return EOF;
  if (__fflush4(stream,BUFINPUT)) return EOF;
  if (stream->bm>=stream->bs) {
    Int len=VG_(read)(stream->fd,stream->buf,stream->buflen);
    if (len==0) {
      stream->flags|=EOFINDICATOR;
      return EOF;
    } else if (len<0) {
kaputt:
      stream->flags|=ERRORINDICATOR;
      return EOF;
    }
    stream->bm=0;
    stream->bs=len;
  }
  c=stream->buf[stream->bm];
  ++stream->bm;
  return c;
}

char *fgets(char *s, int size, FILE *stream) {
  char *orig=s;
  int l;
  for (l=size; l>1;) {
    register int c=fgetc(stream);
    if (c==EOF) break;
    *s=c;
    ++s;
    --l;
    if (c=='\n') break;
  }
  if (l==size || ferror(stream))
    return 0;
  *s=0;
  return orig;
}

size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream) {
  int res;
  unsigned long i,j;
  j=size*nmemb;
  i=0;

  if (!(stream->flags&CANREAD)) {
    stream->flags|=ERRORINDICATOR;
    return 0;
  }
  if (!j || j/nmemb!=size) return 0;
  if (stream->ungotten) {
    stream->ungotten=0;
    *(char*)ptr=stream->ungetbuf;
    ++i;
    if (j==1) return 1;
  }

  if ( !(stream->flags&FDPIPE) && (j>stream->buflen)) {
    size_t tmp=j-i;
    size_t inbuf=stream->bs-stream->bm;
    VG_(memcpy)((char *)ptr+i,(char *)stream->buf+stream->bm,inbuf);
    stream->bm=stream->bs=0;
    tmp-=inbuf;
    i+=inbuf;
    if (fflush(stream)) return 0;
    while ((res=VG_(read)(stream->fd,(char *)ptr+i,tmp))<(Int)tmp) {
      if (res==-1) {
        stream->flags|=ERRORINDICATOR;
        goto exit;
      } else if (!res) {
        stream->flags|=EOFINDICATOR;
        goto exit;
      }
      i+=res; tmp-=res;
    }
    return nmemb;
  }

  for (; i<j; ++i) {
    res=fgetc(stream);
    if (res==EOF)
exit:
      return i/size;
    else
      ((unsigned char*)ptr)[i]=(unsigned char)res;
  }
  return nmemb;
}


int fputc(int c, FILE *stream) {
  if (!(stream->flags&CANWRITE) || __fflush4(stream,0)) {
kaputt:
    stream->flags|=ERRORINDICATOR;
    return EOF;
  }
  if (stream->bm>=stream->buflen-1)
    if (fflush(stream)) goto kaputt;
  if (stream->flags&NOBUF) {
    char ch = c;
    if (VG_(write)(stream->fd,&ch,1) != 1)
      goto kaputt;
    return 0;
  }
  stream->buf[stream->bm]=c;
  ++stream->bm;
  if (((stream->flags&BUFLINEWISE) && c=='\n') ||
      ((stream->flags&NOBUF))) /* puke */
    if (fflush(stream)) goto kaputt;
  return 0;
}

#undef putc
int putc(int c, FILE *stream) {
  return fputc(c, stream);
}

#undef putchar
int putchar(int c) {
  return fputc(c,stdout);
}

size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream)
 {
  Int res;
  unsigned long len=size*nmemb;
  long i;
  if (!(stream->flags&CANWRITE)) {
    stream->flags|=ERRORINDICATOR;
    return 0;
  }
  if (!nmemb || len/nmemb!=size) return 0; /* check for integer overflow */
  if (len>stream->buflen || (stream->flags&NOBUF)) {
    if (fflush(stream)) return 0;
    do {
      res=VG_(write)(stream->fd,ptr,len);
    } while (res==-1 && errno==VKI_EINTR);
  } else {
    register const unsigned char *c=ptr;
    for (i=len; i>0; --i,++c)
      if (fputc(*c,stream)) { res=len-i; goto abort; }
    res=len;
  }
  if (res<0) {
    stream->flags|=ERRORINDICATOR;
    return 0;
  }
abort:
  return size?res/size:0;
}

int fputs(const char*s,FILE*stream) {
  return fwrite(s,VG_(strlen)(s),1,stream);
}

static int __stdio_outs(const char *s,UInt len) {
  return (VG_(write)(1,s,len)==(Int)len)?1:0;
}

int puts(const char *s) {
  return (__stdio_outs(s,VG_(strlen)(s)) && __stdio_outs("\n",1))?0:-1;
}

struct arg_printf {
  void *data;
  int (*put)(void*,size_t,void*);
};

static inline unsigned long skip_to(const char *format) {
  unsigned long nr;
  for (nr=0; format[nr] && (format[nr]!='%'); ++nr);
  return nr;
}

#define A_WRITE(fn,buf,sz)      ((fn)->put((void*)(buf),(sz),(fn)->data))

static const char pad_line[2][16]= { "                ", "0000000000000000", };
static inline int write_pad(struct arg_printf* fn, int len, int padwith) {
  int nr=0;
  for (;len>15;len-=16,nr+=16) {
    A_WRITE(fn,pad_line[(padwith=='0')?1:0],16);
  }
  if (len>0) {
    A_WRITE(fn,pad_line[(padwith=='0')?1:0],(unsigned int)len); nr+=len;
  }
  return nr;
}

static void *my_memmove(void *dst, const void *src, size_t count)
{
  char *a = dst;
  const char *b = src;
  if (src!=dst)
  {
    if (src>dst)
    {
      while (count--) *a++ = *b++;
    }
    else
    {
      a+=count-1;
      b+=count-1;
      while (count--) *a-- = *b--;
    }
  }
  return dst;
}

static int __lltostr(char *s, int size, unsigned long long i, int base,
		     char UpCase)
{
  char *tmp;
  unsigned int j=0;

  s[--size]=0;

  tmp=s+size;

  if ((base==0)||(base>36)) base=10;

  j=0;
  if (!i)
  {
    *(--tmp)='0';
    j=1;
  }

  while((tmp>s)&&(i))
  {
    tmp--;
    if ((*tmp=i%base+'0')>'9') *tmp+=(UpCase?'A':'a')-'9'-1;
    i=i/base;
    j++;
  }
  my_memmove(s,tmp,j+1);

  return j;
}

static int __ltostr(char *s, unsigned int size, unsigned long i,
		    unsigned int base, int UpCase)
{
  char *tmp;
  unsigned int j=0;

  s[--size]=0;

  tmp=s+size;

  if ((base==0)||(base>36)) base=10;

  j=0;
  if (!i)
  {
    *(--tmp)='0';
    j=1;
  }

  while((tmp>s)&&(i))
  {
    tmp--;
    if ((*tmp=i%base+'0')>'9') *tmp+=(UpCase?'A':'a')-'9'-1;
    i=i/base;
    j++;
  }
  my_memmove(s,tmp,j+1);

  return j;
}

// no longer referenced (markro)
#if 0

static int copystring(char* buf,int maxlen, const char* s) {
  int i;
  for (i=0; i<3&&i<maxlen; ++i)
    buf[i]=s[i];
  if (i<maxlen) { buf[i]=0; ++i; }
  return i;
}

static int my_isinf(double d) {
  union {
    unsigned long long l;
    double d;
  } u;
  u.d=d;
  return (u.l==0x7FF0000000000000ll?1:u.l==0xFFF0000000000000ll?-1:0);
}

static int my_isnan(double d) {
  union {
    unsigned long long l;
    double d;
  } u;
  u.d=d;
  return (u.l & 0x7FF0000000000000LL) == 0x7FF0000000000000LL &&
    (u.l & 0xfffffffffffffLL) != 0;
}

static int __dtostr(double d,char *buf,int maxlen,
		    int prec,int prec2,int g) {
  union {
    unsigned long long l;
    double d;
  } u = { .d=d };
  /* step 1: extract sign, mantissa and exponent */
  signed long e=((u.l>>52)&((1<<11)-1))-1023;
/*  unsigned long long m=u.l & ((1ull<<52)-1); */
  /* step 2: exponent is base 2, compute exponent for base 10 */
  signed long e10;
  /* step 3: calculate 10^e10 */
  int i;
  double backup=d;
  double tmp;
  char *oldbuf=buf;

  if ((i=my_isinf(d))) return copystring(buf,maxlen,i>0?"inf":"-inf");
  if (my_isnan(d)) return copystring(buf,maxlen,"nan");
  e10=1+(long)(e*0.30102999566398119802); /* log10(2) */
  /* Wir iterieren von Links bis wir bei 0 sind oder maxlen erreicht
   * ist.  Wenn maxlen erreicht ist, machen wir das nochmal in
   * scientific notation.  Wenn dann von prec noch was übrig ist, geben
   * wir einen Dezimalpunkt aus und geben prec2 Nachkommastellen aus.
   * Wenn prec2 Null ist, geben wir so viel Stellen aus, wie von prec
   * noch übrig ist. */
  if (d==0.0) {
    prec2=prec2==0?1:prec2+2;
    prec2=prec2>maxlen?8:prec2;
    i=0;
    if (prec2 && (long long)u.l<0) { buf[0]='-'; ++i; }
    for (; i<prec2; ++i) buf[i]='0';
    buf[buf[0]=='0'?1:2]='.'; buf[i]=0;
    return i;
  }

  if (d < 0.0) { d=-d; *buf='-'; --maxlen; ++buf; }

   /*
      Perform rounding. It needs to be done before we generate any
      digits as the carry could propagate through the whole number.
   */

  tmp = 0.5;
  for (i = 0; i < prec2; i++) { tmp *= 0.1; }
  d += tmp;

  if (d < 1.0) { *buf='0'; --maxlen; ++buf; }
/*  printf("e=%d e10=%d prec=%d\n",e,e10,prec); */
  if (e10>0) {
    int first=1;	/* are we about to write the first digit? */
    int j = 0;
    tmp = 10.0;
    i=e10;
    while (i>10) { tmp=tmp*1e10; i-=10; }
    while (i>1) { tmp=tmp*10; --i; }
    /* the number is greater than 1. Iterate through digits before the
     * decimal point until we reach the decimal point or maxlen is
     * reached (in which case we switch to scientific notation). */
    while (tmp>0.9) {
      char digit;
      double fraction=d/tmp;
	digit=(int)(fraction);		/* floor() */
      if (!first || digit) {
	j++;
	first=0;
	*buf=digit+'0'; ++buf;
	if (!maxlen) {
	  /* use scientific notation */
	  int len=__dtostr(backup/tmp,oldbuf,maxlen,prec,prec2,0);
	  int initial=1;
	  if (len==0) return 0;
	  maxlen-=len; buf+=len;
	  if (maxlen>0) {
	    *buf='e';
	    ++buf;
	  }
	  --maxlen;
	  for (len=1000; len>0; len/=10) {
	    if (e10>=len || !initial) {
	      if (maxlen>0) {
		*buf=(e10/len)+'0';
		++buf;
	      }
	      --maxlen;
	      initial=0;
	      e10=e10%len;
	    }
	  }
	  if (maxlen>0) goto fini;
	  return 0;
	}
	d-=digit*tmp;
	--maxlen;
      }
      tmp/=10.0;
    }
  }
  else
  {
     tmp = 0.1;
  }

  if (buf==oldbuf) {
    if (!maxlen) return 0; --maxlen;
    *buf='0'; ++buf;
  }
  if (prec2 || prec>(buf-oldbuf)+1) {	/* more digits wanted */
    if (!maxlen) return 0; --maxlen;
    *buf='.'; ++buf;
    if (g) {
      if (prec2) prec=prec2;
      prec-=buf-oldbuf-1;
    } else {
      prec-=buf-oldbuf-1;
      if (prec2) prec=prec2;
    }
    if (prec>maxlen) return 0;
    while (prec>0) {
      char digit;
      double fraction=d/tmp;
      digit=(int)(fraction);		/* floor() */
      *buf=digit+'0'; ++buf;
      d-=digit*tmp;
      tmp/=10.0;
      --prec;
    }
  }
fini:
  *buf=0;
  return buf-oldbuf;
}

#endif

static int __v_printf(struct arg_printf* fn, const char *format,
		      va_list arg_ptr)
{
  int len=0;
#ifdef WANT_ERROR_PRINTF
  int _errno = errno;
#endif

  while (*format) {
    unsigned long sz = skip_to(format);
    if (sz) {
      A_WRITE(fn,format,sz); len+=sz;
      format+=sz;
    }
    if (*format=='%') {
      char buf[1024];
      union { char*s; } u_str;
#define s u_str.s

      int retval;
      unsigned char ch, padwith=' ';

      char flag_in_sign=0;
      char flag_upcase=0;
      char flag_hash=0;
      char flag_left=0;
      char flag_space=0;
      char flag_sign=0;
      char flag_dot=0;
      signed char flag_long=0;

      unsigned int base;
      unsigned int width=0, preci=0;

      long number=0;
      long long llnumber=0;

      ++format;
inn_printf:
      switch(ch=*format++) {
      case 0:
	return -1;
	break;

      /* FLAGS */
      case '#':
	flag_hash=-1;
      case 'z':
	goto inn_printf;

      case 'h':
	--flag_long;
	goto inn_printf;
#if __WORDSIZE != 64
      case 'j':
#endif
      case 'q':		/* BSD ... */
      case 'L':
	++flag_long;
        /* Fall through.  */
#if __WORDSIZE == 64
        /* Fall through.  */
      case 'j':
#endif
      case 'l':
	++flag_long;
	goto inn_printf;

      case '-':
	flag_left=1;
	goto inn_printf;

      case ' ':
	flag_space=1;
	goto inn_printf;

      case '+':
	flag_sign=1;
	goto inn_printf;

      case '0':
      case '1':
      case '2':
      case '3':
      case '4':
      case '5':
      case '6':
      case '7':
      case '8':
      case '9':
	if(flag_dot) return -1;
	width=strtoul(format-1,(char**)&s,10);
	if (ch=='0' && !flag_left) padwith='0';
	format=s;
	goto inn_printf;

      case '*':
	width=va_arg(arg_ptr,int);
	goto inn_printf;

      case '.':
	flag_dot=1;
	if (*format=='*') {
	  int tmp=va_arg(arg_ptr,int);
	  preci=tmp<0?0:tmp;
	  ++format;
	} else {
	  long int tmp=strtol(format,(char**)&s,10);
	  preci=tmp<0?0:tmp;
	  format=s;
	}
	goto inn_printf;

      /* print a char or % */
      case 'c':
	ch=(char)va_arg(arg_ptr,int);
        /* Fall through.  */
      case '%':
	A_WRITE(fn,&ch,1); ++len;
	break;

#ifdef WANT_ERROR_PRINTF
      /* print an error message */
      case 'm':
	s=my_strerror(_errno);
	sz=VG_(strlen)(s);
	A_WRITE(fn,s,sz); len+=sz;
	break;
#endif
      /* print a string */
      case 's':
	s=va_arg(arg_ptr,char *);
	if (!s) s=(char*)("(null)");
	sz = VG_(strlen)(s);
	if (flag_dot && sz>preci) sz=preci;
	preci=0;
	flag_dot^=flag_dot;
	padwith=' ';

print_out:
      {
	char *sign=s;
	int todo=0;
	int vs;

	if (! (width||preci) ) {
	  A_WRITE(fn,s,sz); len+=sz;
	  break;
	}

	if (flag_in_sign) todo=1;
	if (flag_hash>0)  todo=flag_hash;
	if (todo) {
	  s+=todo;
	  sz-=todo;
	  width-=todo;
	}

	if (!flag_left) {
	  if (flag_dot) {
	    vs=preci>sz?preci:sz;
	    len+=write_pad(fn,(signed int)width-(signed int)vs,' ');
	    if (todo) {
	      A_WRITE(fn,sign,todo);
	      len+=todo;
	    }
	    len+=write_pad(fn,(signed int)preci-(signed int)sz,'0');
	  } else {
	    if (todo && padwith=='0') {
	      A_WRITE(fn,sign,todo);
	      len+=todo; todo=0;
	    }
	    len+=write_pad(fn,(signed int)width-(signed int)sz, padwith);
	    if (todo) {
	      A_WRITE(fn,sign,todo);
	      len+=todo;
	    }
	  }
	  A_WRITE(fn,s,sz); len+=sz;
	} else if (flag_left) {
	  if (todo) {
	    A_WRITE(fn,sign,todo);
	    len+=todo;
	  }
	  len+=write_pad(fn,(signed int)preci-(signed int)sz, '0');
	  A_WRITE(fn,s,sz); len+=sz;
	  vs=preci>sz?preci:sz;
	  len+=write_pad(fn,(signed int)width-(signed int)vs, ' ');
	} else {
	  A_WRITE(fn,s,sz); len+=sz;
	}
	break;
      }

      /* print an integer value */
      case 'b':
	base=2;
	sz=0;
	goto num_printf;
      case 'p':
	flag_hash=2;
	flag_long=1;
	ch='x';
        /* Fall through.  */
      case 'X':
	flag_upcase=(ch=='X');
        /* Fall through.  */
      case 'x':
	base=16;
	sz=0;
	if (flag_hash) {
	  buf[1]='0';
	  buf[2]=ch;
	  flag_hash=2;
	  sz=2;
	}
	if (preci>width) width=preci;
	goto num_printf;
      case 'd':
      case 'i':
	flag_in_sign=1;
        /* Fall through.  */
      case 'u':
	base=10;
	sz=0;
	goto num_printf;
      case 'o':
	base=8;
	sz=0;
	if (flag_hash) {
	  buf[1]='0';
	  flag_hash=1;
	  ++sz;
	}

num_printf:
	s=buf+1;

	if (flag_long>0) {
	  if (flag_long>1)
	    llnumber=va_arg(arg_ptr,long long);
	  else
	    number=va_arg(arg_ptr,long);
	}
	else {
	  number=va_arg(arg_ptr,int);
	  if (sizeof(int) != sizeof(long) && !flag_in_sign)
	    number&=((unsigned int)-1);
	}

	if (flag_in_sign) {
	  if ((flag_long>1)&&(llnumber<0)) {
	    llnumber=-llnumber;
	    flag_in_sign=2;
	  } else
	    if (number<0) {
	      number=-number;
	      flag_in_sign=2;
	    }
	}
	if (flag_long<0) number&=0xffff;
	if (flag_long<-1) number&=0xff;
	if (flag_long>1)
	  retval = __lltostr(s+sz,sizeof(buf)-5,(unsigned long long) llnumber,base,flag_upcase);
	else
	  retval = __ltostr(s+sz,sizeof(buf)-5,(unsigned long) number,base,flag_upcase);

	/* When 0 is printed with an explicit precision 0, the output is empty. */
	if (flag_dot && retval == 1 && s[sz] == '0') {
	  if (preci == 0||flag_hash > 0) {
	    sz = 0;
	  }
	  flag_hash = 0;
	} else sz += retval;

	if (flag_in_sign==2) {
	  *(--s)='-';
	  ++sz;
	} else if ((flag_in_sign)&&(flag_sign || flag_space)) {
	  *(--s)=(flag_sign)?'+':' ';
	  ++sz;
	} else flag_in_sign=0;

	goto print_out;

      /* print a floating point value */
      case 'f':
      case 'g':
	{
	  double d=va_arg(arg_ptr,double);
	  s=buf+1;
	  if (width==0) width=1;
	  if (!flag_dot) preci=6;
	  if (flag_sign || d < +0.0) flag_in_sign=1;

	  fptostr(d, width, preci, 'g', s, sizeof(buf)-1);

/* 	  sz=__dtostr(d,s,sizeof(buf)-1,width,preci,g); */

/* 	  if (flag_dot) { */
/* 	    char *tmp; */
/* 	    if ((tmp=VG_(strchr)(s,'.'))) { */
/* 	      if (preci || flag_hash) ++tmp; */
/* 	      while (preci>0 && *++tmp) --preci; */
/* 	      *tmp=0; */
/* 	    } else if (flag_hash) { */
/* 	      s[sz]='.'; */
/* 	      s[++sz]='\0'; */
/* 	    } */
/* 	  } */

/* 	  if (g) { */
/* 	    char *tmp,*tmp1;	/\* boy, is _this_ ugly! *\/ */
/* 	    if ((tmp=VG_(strchr)(s,'.'))) { */
/* 	      tmp1=VG_(strchr)(tmp,'e'); */
/* 	      while (*tmp) ++tmp; */
/* 	      if (tmp1) tmp=tmp1; */
/* 	      while (*--tmp=='0') ; */
/* 	      if (*tmp!='.') ++tmp; */
/* 	      *tmp=0; */
/* 	      if (tmp1) VG_(strcpy)(tmp,tmp1); */
/* 	    } */
/* 	  } */

/* 	  if ((flag_sign || flag_space) && d>=0) { */
/* 	    *(--s)=(flag_sign)?'+':' '; */
/* 	    ++sz; */
/* 	  } */

	  sz=VG_(strlen)(s);
	  flag_dot=0;
	  flag_hash=0;
	  goto print_out;
	}

      default:
	break;
      }
    }
  }
  return len;
}
#undef s

static int __vfp_fwrite(void*ptr, size_t nmemb, FILE* f) {
  return fwrite(ptr,1,nmemb,f);
}

int vfprintf(FILE *stream, const char *format, va_list arg_ptr)
{
  struct arg_printf ap = { stream, (int(*)(void*,size_t,void*)) __vfp_fwrite };
  return __v_printf(&ap,format,arg_ptr);
}

int fprintf(FILE *f, const char *format, ...) {
  int n;
  va_list arg_ptr;
  va_start(arg_ptr,format);
  n=vfprintf(f,format,arg_ptr);
  va_end(arg_ptr);
  return n;
}

int vprintf(const char *format, va_list ap)
{
  struct arg_printf _ap = { 0, (int(*)(void*,size_t,void*)) __stdio_outs };
  return __v_printf(&_ap,format,ap);
}

int printf(const char *format, ...)
{
  int n;
  va_list arg_ptr;
  va_start(arg_ptr, format);
  n=vprintf(format, arg_ptr);
  va_end(arg_ptr);
  return n;
}

struct str_data {
  char* str;
  size_t len;
  size_t size;
};

static int swrite(void*ptr, size_t nmemb, struct str_data* sd) {
  size_t tmp=sd->size-sd->len;
  if (tmp>0) {
    size_t len=nmemb;
    if (len>tmp) len=tmp;
    if (sd->str) {
      VG_(memcpy)(sd->str+sd->len,ptr,len);
      sd->str[sd->len+len]=0;
    }
    sd->len+=len;
  }
  return nmemb;
}

int vsnprintf(char* dest, size_t size, const char *format, va_list arg_ptr)
{
  int n;
  struct str_data sd = { dest, 0, size?size-1:0 };
  struct arg_printf ap = { &sd, (int(*)(void*,size_t,void*)) swrite };
  n=__v_printf(&ap,format,arg_ptr);
  if (dest && size && n>=0) {
    if (size!=(size_t)-1 && ((size_t)n>=size)) dest[size-1]=0;
    else dest[n]=0;
  }
  return n;
}

int snprintf(char *dest, size_t size, const char *format, ...)
{
  int n;
  va_list arg_ptr;
  va_start(arg_ptr, format);
  n=vsnprintf(dest,size,format,arg_ptr);
  va_end(arg_ptr);
  return n;
}

int vsprintf(char *dest, const char *format, va_list arg_ptr)
{
  return vsnprintf(dest,(size_t)-1,format,arg_ptr);
}

int sprintf(char *dest, const char *format, ...)
{
  int n;
  va_list arg_ptr;
  va_start(arg_ptr, format);
  n=vsprintf(dest,format,arg_ptr);
  va_end (arg_ptr);
  return n;
}

int fseek(FILE *stream, long offset, int whence) {
  fflush(stream);
  stream->bm=0; stream->bs=0;
  stream->flags&=~(ERRORINDICATOR|EOFINDICATOR);
  stream->ungotten=0;
  return VG_(lseek)(stream->fd,offset,whence)!=-1?0:-1;
}

long ftell(FILE *stream) {
  vki_off_t l;
  if (fflush(stream)) return -1;
  l=VG_(lseek)(stream->fd,0,VKI_SEEK_CUR);
  if (l==-1) return -1;
  return l-stream->ungotten;
}

/* stdlib.h */

// rename from abort to avoid conflict with coregrind::abort (markro)
void my_abort(void) {
    tl_assert(0);
}

#define ERANGE 34

unsigned long int strtoul(const char *ptr, char **endptr, int base)
{
  int neg = 0, overflow = 0;
  unsigned long int v=0;
  const char* orig;
  const char* nptr=ptr;

  while(isspace(*nptr)) ++nptr;

  if (*nptr == '-') { neg=1; nptr++; }
  else if (*nptr == '+') ++nptr;
  orig=nptr;
  if (base==16 && nptr[0]=='0') goto skip0x;
  if (base) {
    register unsigned int b=base-2;
    if (b>34) { errno=VKI_EINVAL; return 0; }
  } else {
    if (*nptr=='0') {
      base=8;
skip0x:
      if ((nptr[1]=='x'||nptr[1]=='X') && isxdigit(nptr[2])) {
        nptr+=2;
        base=16;
      }
    } else
      base=10;
  }
  while(*nptr) {
    register unsigned char c=*nptr;
    c=(c>='a'?c-'a'+10:c>='A'?c-'A'+10:c<='9'?c-'0':0xff);
    if (c>=base) break;     /* out of base */
    {
      register unsigned long x=(v&0xff)*base+c;
      register unsigned long w=(v>>8)*base+(x>>8);
      if (w>(ULONG_MAX>>8)) overflow=1;
      v=(w<<8)+(x&0xff);
    }
    ++nptr;
  }
  if (nptr==orig) {         /* no conversion done */
    nptr=ptr;
    errno=VKI_EINVAL;
    v=0;
  }
  if (endptr) *endptr=(char *)nptr;
  if (overflow) {
    errno=ERANGE;
    return ULONG_MAX;
  }
  return (neg?-v:v);
}


#if __WORDSIZE == 64
#define ABS_LONG_MIN 9223372036854775808UL
#else
#define ABS_LONG_MIN 2147483648UL
#endif
long int strtol(const char *nptr, char **endptr, int base)
{
  int neg=0;
  unsigned long int v;
  const char*orig=nptr;

  while(isspace(*nptr)) nptr++;

  if (*nptr == '-' && isalnum(nptr[1])) { neg=-1; ++nptr; }
  v=strtoul(nptr,endptr,base);
  if (endptr && *endptr==nptr) *endptr=(char *)orig;
  if (v>=ABS_LONG_MIN) {
    if (v==ABS_LONG_MIN && neg) {
      errno=0;
      return v;
    }
    errno=ERANGE;
    return (neg?LONG_MIN:LONG_MAX);
  }
  return (neg?-v:v);
}

int atoi(const char* s) {
  long int v=0;
  int sign=1;
  while ( *s == ' '  ||  (unsigned int)(*s - 9) < 5u) s++;
  switch (*s) {
  case '-': sign=-1;
            /* Fall through.  */
  case '+': ++s;
  }
  while ((unsigned int) (*s - '0') < 10u) {
    v=v*10+*s-'0'; ++s;
  }
  return sign==-1?-v:v;
}

/* string.h */

static size_t my_strspn(const char *s, const char *accept)
{
  size_t l=0;
  int a=1,i,al=VG_(strlen)(accept);

  while((a)&&(*s))
  {
    for(a=i=0;(!a)&&(i<al);i++)
      if (*s==accept[i]) a=1;
    if (a) l++;
    s++;
  }
  return l;
}

static size_t my_strcspn(const char *s, const char *reject)
{
  size_t l=0;
  int a=1,i,al=VG_(strlen)(reject);

  while((a)&&(*s))
  {
    for(i=0;(a)&&(i<al);i++)
      if (*s==reject[i]) a=0;
    if (a) l++;
    s++;
  }
  return l;
}

static char* strtok_r(char*s,const char*delim,char**ptrptr) {
  char*tmp=0;

  if (s==0) s=*ptrptr;
  s+=my_strspn(s,delim);           /* overread leading delimiter */
  if (*s) {
    tmp=s;
    s+=my_strcspn(s,delim);
    if (*s) *s++=0;   /* not the end ? => terminate it */
  }
  *ptrptr=s;
  return tmp;
}


static char *strtok_pos;

char *strtok(char *s, const char *delim)
{
  return strtok_r(s,delim,&strtok_pos);
}

/* Copied from coregrind/m_syscall.c, since that version isn't
   exported to tools! */
const char* my_strerror(int errnum)
{
   switch (errnum) {
      case VKI_EPERM:       return "Operation not permitted";
      case VKI_ENOENT:      return "No such file or directory";
      case VKI_ESRCH:       return "No such process";
      case VKI_EINTR:       return "Interrupted system call";
      case VKI_EBADF:       return "Bad file number";
      case VKI_EAGAIN:      return "Try again";
      case VKI_ENOMEM:      return "Out of memory";
      case VKI_EACCES:      return "Permission denied";
      case VKI_EFAULT:      return "Bad address";
      case VKI_EEXIST:      return "File exists";
      case VKI_EINVAL:      return "Invalid argument";
      case VKI_EMFILE:      return "Too many open files";
      case VKI_ENOSYS:      return "Function not implemented";
      case VKI_ERESTARTSYS: return "ERESTARTSYS";
      default:              return "strerror: unknown error";
   }
}

/* unistd.h */
int mkfifo(const char *fn, __mode_t mode) {
  SysRes res = VG_(mknod)(fn, mode|VKI_S_IFIFO, 0);
  if (sr_isError(res)) {
    errno = sr_Err(res);
    return -1;
  } else {
    return sr_Res(res);
  }
}
