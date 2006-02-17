
/*--------------------------------------------------------------------*/
/*--- File- and socket-related libc stuff.            m_libcfile.c ---*/
/*--------------------------------------------------------------------*/
 
/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Julian Seward 
      jseward@acm.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_core_basics.h"
#include "pub_core_libcbase.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcfile.h"
#include "pub_core_libcprint.h"     // VG_(sprintf)
#include "pub_core_libcproc.h"      // VG_(getpid), VG_(getppid)
#include "pub_core_clientstate.h"   // VG_(fd_hard_limit)
#include "pub_core_syscall.h"
#include "vki_unistd.h"

/* ---------------------------------------------------------------------
   File stuff
   ------------------------------------------------------------------ */

static inline Bool fd_exists(Int fd)
{
   struct vki_stat st;

   return VG_(fstat)(fd, &st) == 0;
}

/* Move an fd into the Valgrind-safe range */
Int VG_(safe_fd)(Int oldfd)
{
   Int newfd;

   vg_assert(VG_(fd_hard_limit) != -1);

   newfd = VG_(fcntl)(oldfd, VKI_F_DUPFD, VG_(fd_hard_limit));
   if (newfd != -1)
      VG_(close)(oldfd);

   VG_(fcntl)(newfd, VKI_F_SETFD, VKI_FD_CLOEXEC);

   vg_assert(newfd >= VG_(fd_hard_limit));
   return newfd;
}

/* Given a file descriptor, attempt to deduce its filename.  To do
   this, we use /proc/self/fd/<FD>.  If this doesn't point to a file,
   or if it doesn't exist, we return False. */
Bool VG_(resolve_filename) ( Int fd, HChar* buf, Int n_buf )
{
   HChar tmp[64];

   VG_(sprintf)(tmp, "/proc/self/fd/%d", fd);
   VG_(memset)(buf, 0, n_buf);

   if (VG_(readlink)(tmp, buf, n_buf) > 0 && buf[0] == '/')
      return True;
   else
      return False;
}

SysRes VG_(open) ( const Char* pathname, Int flags, Int mode )
{  
   SysRes res = VG_(do_syscall3)(__NR_open, (UWord)pathname, flags, mode);
   return res;
}

void VG_(close) ( Int fd )
{
   (void)VG_(do_syscall1)(__NR_close, fd);
}

Int VG_(read) ( Int fd, void* buf, Int count)
{
   SysRes res = VG_(do_syscall3)(__NR_read, fd, (UWord)buf, count);
   return res.isError ? -1 : res.val;
}

Int VG_(write) ( Int fd, const void* buf, Int count)
{
   SysRes res = VG_(do_syscall3)(__NR_write, fd, (UWord)buf, count);
   return res.isError ? -1 : res.val;
}

Int VG_(pipe) ( Int fd[2] )
{
   SysRes res = VG_(do_syscall1)(__NR_pipe, (UWord)fd);
   return res.isError ? -1 : 0;
}

OffT VG_(lseek) ( Int fd, OffT offset, Int whence )
{
   SysRes res = VG_(do_syscall3)(__NR_lseek, fd, offset, whence);
   return res.isError ? (-1) : res.val;
   /* if you change the error-reporting conventions of this, also
      change VG_(pread) and all other usage points. */
}

SysRes VG_(stat) ( Char* file_name, struct vki_stat* buf )
{
   SysRes res = VG_(do_syscall2)(__NR_stat, (UWord)file_name, (UWord)buf);
   return res;
}

Int VG_(fstat) ( Int fd, struct vki_stat* buf )
{
   SysRes res = VG_(do_syscall2)(__NR_fstat, fd, (UWord)buf);
   return res.isError ? (-1) : 0;
}

Int VG_(fsize) ( Int fd )
{
   struct vki_stat buf;
   SysRes res = VG_(do_syscall2)(__NR_fstat, fd, (UWord)&buf);
   return res.isError ? (-1) : buf.st_size;
}

Bool VG_(is_dir) ( HChar* f )
{
   struct vki_stat buf;
   SysRes res = VG_(do_syscall2)(__NR_stat, (UWord)f, (UWord)&buf);
   return res.isError ? False
                      : VKI_S_ISDIR(buf.st_mode) ? True : False;
}

SysRes VG_(dup) ( Int oldfd )
{
   return VG_(do_syscall1)(__NR_dup, oldfd);
}

/* Returns -1 on error. */
Int VG_(fcntl) ( Int fd, Int cmd, Int arg )
{
   SysRes res = VG_(do_syscall3)(__NR_fcntl, fd, cmd, arg);
   return res.isError ? -1 : res.val;
}

Int VG_(rename) ( Char* old_name, Char* new_name )
{
   SysRes res = VG_(do_syscall2)(__NR_rename, (UWord)old_name, (UWord)new_name);
   return res.isError ? (-1) : 0;
}

Int VG_(unlink) ( Char* file_name )
{
   SysRes res = VG_(do_syscall1)(__NR_unlink, (UWord)file_name);
   return res.isError ? (-1) : 0;
}

/* Nb: we do not allow the Linux extension which malloc()s memory for the
   buffer if buf==NULL, because we don't want Linux calling malloc() */
Bool VG_(getcwd) ( Char* buf, SizeT size )
{
   SysRes res;
   vg_assert(buf != NULL);
   res = VG_(do_syscall2)(__NR_getcwd, (UWord)buf, size);
   return res.isError ? False : True;
}

Int VG_(readlink) (Char* path, Char* buf, UInt bufsiz)
{
   SysRes res;
   /* res = readlink( path, buf, bufsiz ); */
   res = VG_(do_syscall3)(__NR_readlink, (UWord)path, (UWord)buf, bufsiz);
   return res.isError ? -1 : res.val;
}

Int VG_(getdents) (UInt fd, struct vki_dirent *dirp, UInt count)
{
   SysRes res;
   /* res = getdents( fd, dirp, count ); */
   res = VG_(do_syscall3)(__NR_getdents, fd, (UWord)dirp, count);
   return res.isError ? -1 : res.val;
}

/* Check accessibility of a file.  Returns zero for access granted,
   nonzero otherwise. */
Int VG_(access) ( HChar* path, Bool irusr, Bool iwusr, Bool ixusr )
{
#if defined(VGO_linux)
   /* Very annoyingly, I cannot find any definition for R_OK et al in
      the kernel interfaces.  Therefore I reluctantly resort to
      hardwiring in these magic numbers that I determined by
      experimentation. */
   UWord w = (irusr ? 4/*R_OK*/ : 0)
             | (iwusr ? 2/*W_OK*/ : 0)
             | (ixusr ? 1/*X_OK*/ : 0);
   SysRes res = VG_(do_syscall2)(__NR_access, (UWord)path, w);
   return res.isError ? 1 : res.val;
#else
#  error "Don't know how to do VG_(access) on this OS"
#endif
}

/* 
   Emulate the normal Unix permissions checking algorithm.

   If owner matches, then use the owner permissions, else
   if group matches, then use the group permissions, else
   use other permissions.

   Note that we can't deal with SUID/SGID, so we refuse to run them
   (otherwise the executable may misbehave if it doesn't have the
   permissions it thinks it does).
*/
/* returns: 0 = success, non-0 is failure */
Int VG_(check_executable)(HChar* f)
{
   struct vki_stat st;
   SysRes res;

   res = VG_(stat)(f, &st);
   if (res.isError) {
      return res.val;
   }

   if (st.st_mode & (VKI_S_ISUID | VKI_S_ISGID)) {
      //VG_(printf)("Can't execute suid/sgid executable %s\n", exe);
      return VKI_EACCES;
   }

   if (VG_(geteuid)() == st.st_uid) {
      if (!(st.st_mode & VKI_S_IXUSR))
         return VKI_EACCES;
   } else {
      int grpmatch = 0;

      if (VG_(getegid)() == st.st_gid)
	 grpmatch = 1;
      else {
	 UInt groups[32];
	 Int ngrp = VG_(getgroups)(32, groups);
	 Int i;
         /* ngrp will be -1 if VG_(getgroups) failed. */
         for (i = 0; i < ngrp; i++) {
	    if (groups[i] == st.st_gid) {
	       grpmatch = 1;
	       break;
	    }
         }
      }

      if (grpmatch) {
	 if (!(st.st_mode & VKI_S_IXGRP)) {
            return VKI_EACCES;
         }
      } else if (!(st.st_mode & VKI_S_IXOTH)) {
         return VKI_EACCES;
      }
   }

   return 0;
}

SysRes VG_(pread) ( Int fd, void* buf, Int count, Int offset )
{
   OffT off = VG_(lseek)( fd, (OffT)offset, VKI_SEEK_SET);
   if (off < 0)
      return VG_(mk_SysRes_Error)( VKI_EINVAL );
   return VG_(do_syscall3)(__NR_read, fd, (UWord)buf, count );
}

/* Create and open (-rw------) a tmp file name incorporating said arg.
   Returns -1 on failure, else the fd of the file.  If fullname is
   non-NULL, the file's name is written into it.  The number of bytes
   written is guaranteed not to exceed 64+strlen(part_of_name). */

Int VG_(mkstemp) ( HChar* part_of_name, /*OUT*/HChar* fullname )
{
   HChar  buf[200];
   Int    n, tries, fd;
   UInt   seed;
   SysRes sres;

   vg_assert(part_of_name);
   n = VG_(strlen)(part_of_name);
   vg_assert(n > 0 && n < 100);

   seed = (VG_(getpid)() << 9) ^ VG_(getppid)();

   tries = 0;
   while (True) {
      if (tries > 10) 
         return -1;
      VG_(sprintf)( buf, "/tmp/valgrind_%s_%08x", 
                         part_of_name, VG_(random)( &seed ));
      if (0)
         VG_(printf)("VG_(mkstemp): trying: %s\n", buf);

      sres = VG_(open)(buf,
                       VKI_O_CREAT|VKI_O_RDWR|VKI_O_EXCL|VKI_O_TRUNC,
                       VKI_S_IRUSR|VKI_S_IWUSR);
      if (sres.isError)
         continue;
      /* VG_(safe_fd) doesn't return if it fails. */
      fd = VG_(safe_fd)( sres.val );
      if (fullname)
         VG_(strcpy)( fullname, buf );
      return fd;
   }
   /* NOTREACHED */
}


/* ---------------------------------------------------------------------
   Socket-related stuff.  This is very Linux-kernel specific.
   ------------------------------------------------------------------ */

static
Int parse_inet_addr_and_port ( UChar* str, UInt* ip_addr, UShort* port );

static
Int my_socket ( Int domain, Int type, Int protocol );

static
Int my_connect ( Int sockfd, struct vki_sockaddr_in* serv_addr, 
                 Int addrlen );

UInt VG_(htonl) ( UInt x )
{
#  if defined(VG_BIGENDIAN)
   return x;
#  else
   return
      (((x >> 24) & 0xFF) << 0) | (((x >> 16) & 0xFF) << 8)
      | (((x >> 8) & 0xFF) << 16) | (((x >> 0) & 0xFF) << 24);
#  endif
}

UInt VG_(ntohl) ( UInt x )
{
#  if defined(VG_BIGENDIAN)
   return x;
#  else
   return
      (((x >> 24) & 0xFF) << 0) | (((x >> 16) & 0xFF) << 8)
      | (((x >> 8) & 0xFF) << 16) | (((x >> 0) & 0xFF) << 24);
#  endif
}

UShort VG_(htons) ( UShort x )
{
#  if defined(VG_BIGENDIAN)
   return x;
#  else
   return
      (((x >> 8) & 0xFF) << 0) | (((x >> 0) & 0xFF) << 8);
#  endif
}

UShort VG_(ntohs) ( UShort x )
{
#  if defined(VG_BIGENDIAN)
   return x;
#  else
   return
      (((x >> 8) & 0xFF) << 0) | (((x >> 0) & 0xFF) << 8);
#  endif
}


/* The main function. 

   Supplied string contains either an ip address "192.168.0.1" or
   an ip address and port pair, "192.168.0.1:1500".  Parse these,
   and return:
     -1 if there is a parse error
     -2 if no parse error, but specified host:port cannot be opened
     the relevant file (socket) descriptor, otherwise.
 is used.
*/
Int VG_(connect_via_socket)( UChar* str )
{
   Int sd, res;
   struct vki_sockaddr_in servAddr;
   UInt   ip   = 0;
   UShort port = VG_CLO_DEFAULT_LOGPORT;
   Bool   ok   = parse_inet_addr_and_port(str, &ip, &port);
   if (!ok) 
      return -1;

   //if (0)
   //   VG_(printf)("ip = %d.%d.%d.%d, port %d\n",
   //               (ip >> 24) & 0xFF, (ip >> 16) & 0xFF, 
   //               (ip >> 8) & 0xFF, ip & 0xFF, 
   //               (UInt)port );

   servAddr.sin_family = VKI_AF_INET;
   servAddr.sin_addr.s_addr = VG_(htonl)(ip);
   servAddr.sin_port = VG_(htons)(port);

   /* create socket */
   sd = my_socket(VKI_AF_INET, VKI_SOCK_STREAM, 0 /* IPPROTO_IP ? */);
   if (sd < 0) {
      /* this shouldn't happen ... nevertheless */
      return -2;
   }
		
   /* connect to server */
   res = my_connect(sd, (struct vki_sockaddr_in *) &servAddr, 
                        sizeof(servAddr));
   if (res < 0) {
      /* connection failed */
      return -2;
   }

   return sd;
}


/* Let d = one or more digits.  Accept either:
   d.d.d.d  or  d.d.d.d:d
*/
Int parse_inet_addr_and_port ( UChar* str, UInt* ip_addr, UShort* port )
{
#  define GET_CH ((*str) ? (*str++) : 0)
   UInt ipa, i, j, c, any;
   ipa = 0;
   for (i = 0; i < 4; i++) {
      j = 0;
      any = 0;
      while (1) {
         c = GET_CH; 
         if (c < '0' || c > '9') break;
         j = 10 * j + (int)(c - '0');
         any = 1;
      }
      if (any == 0 || j > 255) goto syntaxerr;
      ipa = (ipa << 8) + j;
      if (i <= 2 && c != '.') goto syntaxerr;
   }
   if (c == 0 || c == ':') 
      *ip_addr = ipa;
   if (c == 0) goto ok;
   if (c != ':') goto syntaxerr;
   j = 0;
   any = 0;
   while (1) {
      c = GET_CH; 
      if (c < '0' || c > '9') break;
      j = j * 10 + (int)(c - '0');
      any = 1;
      if (j > 65535) goto syntaxerr;
   }
   if (any == 0 || c != 0) goto syntaxerr;
   if (j < 1024) goto syntaxerr;
   *port = (UShort)j;
 ok:
   return 1;
 syntaxerr:
   return 0;
#  undef GET_CH
}

static
Int my_socket ( Int domain, Int type, Int protocol )
{
#if defined(VGP_x86_linux) || defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   SysRes res;
   UWord  args[3];
   args[0] = domain;
   args[1] = type;
   args[2] = protocol;
   res = VG_(do_syscall2)(__NR_socketcall, VKI_SYS_SOCKET, (UWord)&args);
   return res.isError ? -1 : res.val;

#elif defined(VGP_amd64_linux)
   SysRes res;
   res = VG_(do_syscall3)(__NR_socket, domain, type, protocol );
   return res.isError ? -1 : res.val;

#else
#  error Unknown arch
#endif
}

static
Int my_connect ( Int sockfd, struct vki_sockaddr_in* serv_addr, 
                 Int addrlen )
{
#if defined(VGP_x86_linux) || defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   SysRes res;
   UWord  args[3];
   args[0] = sockfd;
   args[1] = (UWord)serv_addr;
   args[2] = addrlen;
   res = VG_(do_syscall2)(__NR_socketcall, VKI_SYS_CONNECT, (UWord)&args);
   return res.isError ? -1 : res.val;

#elif defined(VGP_amd64_linux)
   SysRes res;
   res = VG_(do_syscall3)(__NR_connect, sockfd, (UWord)serv_addr, addrlen);
   return res.isError ? -1 : res.val;

#else
#  error Unknown arch
#endif
}

Int VG_(write_socket)( Int sd, void *msg, Int count )
{
   /* This is actually send(). */
   /* Requests not to send SIGPIPE on errors on stream oriented
      sockets when the other end breaks the connection. The EPIPE
      error is still returned. */
   Int flags = VKI_MSG_NOSIGNAL;

#if defined(VGP_x86_linux) || defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   SysRes res;
   UWord  args[4];
   args[0] = sd;
   args[1] = (UWord)msg;
   args[2] = count;
   args[3] = flags;
   res = VG_(do_syscall2)(__NR_socketcall, VKI_SYS_SEND, (UWord)&args);
   return res.isError ? -1 : res.val;

#elif defined(VGP_amd64_linux)
   SysRes res;
   res = VG_(do_syscall6)(__NR_sendto, sd, (UWord)msg, count, flags, 0,0);
   return res.isError ? -1 : res.val;

#else
#  error Unknown arch
#endif
}

Int VG_(getsockname) ( Int sd, struct vki_sockaddr *name, Int *namelen)
{
   SysRes res;

#if defined(VGP_x86_linux) || defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   UWord  args[3];
   args[0] = sd;
   args[1] = (UWord)name;
   args[2] = (UWord)namelen;
   res = VG_(do_syscall2)(__NR_socketcall, VKI_SYS_GETSOCKNAME, (UWord)&args);
   return res.isError ? -1 : res.val;

#elif defined(VGP_amd64_linux)
   res = VG_(do_syscall3)( __NR_getsockname,
                           (UWord)sd, (UWord)name, (UWord)namelen );
   return res.isError ? -1 : res.val;

#else
#  error Unknown arch
#endif
}

Int VG_(getpeername) ( Int sd, struct vki_sockaddr *name, Int *namelen)
{
   SysRes res;

#if defined(VGP_x86_linux) || defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   UWord  args[3];
   args[0] = sd;
   args[1] = (UWord)name;
   args[2] = (UWord)namelen;
   res = VG_(do_syscall2)(__NR_socketcall, VKI_SYS_GETPEERNAME, (UWord)&args);
   return res.isError ? -1 : res.val;

#elif defined(VGP_amd64_linux)
   res = VG_(do_syscall3)( __NR_getpeername,
                           (UWord)sd, (UWord)name, (UWord)namelen );
   return res.isError ? -1 : res.val;

#else
#  error Unknown archx
#endif
}

Int VG_(getsockopt) ( Int sd, Int level, Int optname, void *optval,
                      Int *optlen)
{
   SysRes res;

#if defined(VGP_x86_linux) || defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   UWord  args[5];
   args[0] = sd;
   args[1] = level;
   args[2] = optname;
   args[3] = (UWord)optval;
   args[4] = (UWord)optlen;
   res = VG_(do_syscall2)(__NR_socketcall, VKI_SYS_GETSOCKOPT, (UWord)&args);
   return res.isError ? -1 : res.val;

#elif defined(VGP_amd64_linux)
   res = VG_(do_syscall5)( __NR_getsockopt,
                           (UWord)sd, (UWord)level, (UWord)optname, 
                           (UWord)optval, (UWord)optlen );
   return res.isError ? -1 : res.val;

#else
#  error Unknown arch
#endif
}



/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/

