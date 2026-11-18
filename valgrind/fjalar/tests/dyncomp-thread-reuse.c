/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

// Runs a thread, and after it exits, runs a second thread, which Valgrind
// puts in the first thread's slot.  The tag garbage collector runs while the
// slot is empty and while the second thread runs.  See
// dyncomp-thread-reuse-test.sh.

#include <pthread.h>
#include <sched.h>
#include <stddef.h>
#include <sys/mman.h>

#define BUFFER_SIZE (1 << 18)

static long sink;

// Creates more tags than the test's --dyncomp-gc-num-tags, because each
// iteration's literals get fresh tags, and then makes a system call.  The
// garbage collector runs only when a thread resumes running client code, such
// as after a system call.
static long churn(long seed) {
  long sum = seed;
  long i;
  for (i = 0; i < 10000; i++) {
    sum = sum * 3 + i;
  }
  sched_yield();
  return sum;
}

static void* work(void* arg) {
  sink += churn((long)arg);
  return NULL;
}

static void run_thread(long seed) {
  pthread_t thread;
  pthread_create(&thread, NULL, work, (void*)seed);
  pthread_join(thread, NULL);
}

int main(void) {
  char* buffer = mmap(NULL, BUFFER_SIZE, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  long i;

  if (buffer == MAP_FAILED) {
    return 1;
  }
  // Gives each byte of buffer a tag of its own.
  for (i = 0; i < BUFFER_SIZE; i++) {
    buffer[i] = 7;
  }
  run_thread(1);
  // Unmapping buffer discards its tags, so the next garbage collection
  // renumbers the tags in use to numbers smaller than those in the guest
  // state of the exited thread's slot.
  munmap(buffer, BUFFER_SIZE);
  sink += churn(2);
  // The new thread's guest state must not contain those stale tags, which
  // the garbage collector finds when it runs during churn.
  run_thread(3);
  return 0;
}
