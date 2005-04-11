#include <sys/socket.h>
#include <unistd.h>
int
main (int argc, char **argv)
{
   int fds[2];

   /*
    * Fedora Core 1's Perl opens /dev/pts/2 as fd 10.  Let's close it
    * now to get consistent results across different releases.
    */

   close(10);

   socketpair(AF_UNIX, SOCK_STREAM, PF_UNIX, fds);
   return 0;
}
