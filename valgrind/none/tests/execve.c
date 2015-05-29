#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

int main(int argc, char **argv)
{
   if (argc == 1)
   {
      // This tests the case where argv and envp are NULL, which is easy to
      // get wrong because it's an unusual case.
#  if !defined(VGO_darwin)
      if (execve("/bin/true", NULL, NULL) < 0)
#  else
      if (execve("/usr/bin/true", NULL, NULL) < 0)          
#  endif
      {
         perror("execve");
         exit(1);
      }
   }
   
   exit(0);
}
