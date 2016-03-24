
/*--------------------------------------------------------------------*/
/*--- System call numbers for tilegx-linux.                         ---*/
/*---                                     vki-scnums-tilegx-linux.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2010-2015 Tilera Corp.

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

/* Contributed by Zhi-Gang Liu <zliu at tilera dot com> */

#ifndef __VKI_SCNUMS_TILEGX_LINUX_H
#define __VKI_SCNUMS_TILEGX_LINUX_H

/* From tilegx linux/include/asm-generic/unistd.h */

#define __NR_io_setup 0
#define __NR_io_destroy 1
#define __NR_io_submit 2
#define __NR_io_cancel 3
#define __NR_io_getevents 4

/* fs/xattr.c */
#define __NR_setxattr 5
#define __NR_lsetxattr 6
#define __NR_fsetxattr 7
#define __NR_getxattr 8
#define __NR_lgetxattr 9
#define __NR_fgetxattr 10
#define __NR_listxattr 11
#define __NR_llistxattr 12
#define __NR_flistxattr 13
#define __NR_removexattr 14
#define __NR_lremovexattr 15
#define __NR_fremovexattr 16

/* fs/dcache.c */
#define __NR_getcwd 17

/* fs/cookies.c */
#define __NR_lookup_dcookie 18

/* fs/eventfd.c */
#define __NR_eventfd2 19

/* fs/eventpoll.c */
#define __NR_epoll_create1 20
#define __NR_epoll_ctl 21
#define __NR_epoll_pwait 22

/* fs/fcntl.c */
#define __NR_dup 23
#define __NR_dup2 23
#define __NR_dup3 24
#define __NR_fcntl 25

/* fs/inotify_user.c */
#define __NR_inotify_init1 26
#define __NR_inotify_add_watch 27
#define __NR_inotify_rm_watch 28

/* fs/ioctl.c */
#define __NR_ioctl 29

/* fs/ioprio.c */
#define __NR_ioprio_set 30
#define __NR_ioprio_get 31

/* fs/locks.c */
#define __NR_flock 32

/* fs/namei.c */
#define __NR_mknodat 33
#define __NR_mkdirat 34
#define __NR_unlinkat 35
#define __NR_symlinkat 36
#define __NR_linkat 37
#define __NR_renameat 38

/* fs/namespace.c */
#define __NR_umount2 39

#define __NR_mount 40
#define __NR_pivot_root 41

/* fs/nfsctl.c */
#define __NR_nfsservctl 42

/* fs/open.c */
#define __NR_statfs 43
#define __NR_fstatfs 44
#define __NR_truncate 45
#define __NR_ftruncate 46
#define __NR_fallocate 47
#define __NR_faccessat 48
#define __NR_chdir 49
#define __NR_fchdir 50
#define __NR_chroot 51
#define __NR_fchmod 52
#define __NR_fchmodat 53
#define __NR_fchownat 54
#define __NR_fchown 55
#define __NR_openat 56
#define __NR_close 57
#define __NR_vhangup 58

/* fs/pipe.c */
#define __NR_pipe2 59

/* fs/quota.c */
#define __NR_quotactl 60

/* fs/readdir.c */
#define __NR_getdents64 61

/* fs/read_write.c */
#define __NR_lseek 62
#define __NR_read 63
#define __NR_write 64
#define __NR_readv 65
#define __NR_writev 66
#define __NR_pread64 67
#define __NR_pwrite64 68
#define __NR_preadv 69
#define __NR_pwritev 70

/* fs/sendfile.c */
#define __NR_sendfile 71

/* fs/select.c */
#define __NR_pselect6 72
#define __NR_ppoll 73

/* fs/signalfd.c */
#define __NR_signalfd4 74

/* fs/splice.c */
#define __NR_vmsplice 75
#define __NR_splice 76
#define __NR_tee 77

/* fs/stat.c */
#define __NR_readlinkat 78
#define __NR3264_fstatat 79
#define __NR_stat     -10000
#define __NR_fstat   80

/* fs/sync.c */
#define __NR_sync 81
#define __NR_fsync 82
#define __NR_fdatasync 83
#define __NR_sync_file_range2 84
#define __NR_sync_file_range 84

/* fs/timerfd.c */
#define __NR_timerfd_create 85
#define __NR_timerfd_settime 86
#define __NR_timerfd_gettime 87

/* fs/utimes.c */
#define __NR_utimensat 88

/* kernel/acct.c */
#define __NR_acct 89

/* kernel/capability.c */
#define __NR_capget 90
#define __NR_capset 91

/* kernel/exec_domain.c */
#define __NR_personality 92

/* kernel/exit.c */
#define __NR_exit 93

#define __NR_exit_group 94
#define __NR_waitid 95

/* kernel/fork.c */
#define __NR_set_tid_address 96
#define __NR_unshare 97

/* kernel/futex.c */
#define __NR_futex 98
#define __NR_set_robust_list 99
#define __NR_get_robust_list 100

/* kernel/hrtimer.c */
#define __NR_nanosleep 101

/* kernel/itimer.c */
#define __NR_getitimer 102
#define __NR_setitimer 103

/* kernel/kexec.c */
#define __NR_kexec_load 104

/* kernel/module.c */
#define __NR_init_module 105
#define __NR_delete_module 106

/* kernel/posix-timers.c */
#define __NR_timer_create 107
#define __NR_timer_gettime 108
#define __NR_timer_getoverrun 109
#define __NR_timer_settime 110
#define __NR_timer_delete 111
#define __NR_clock_settime 112
#define __NR_clock_gettime 113
#define __NR_clock_getres 114
#define __NR_clock_nanosleep 115

/* kernel/printk.c */
#define __NR_syslog 116

/* kernel/ptrace.c */
#define __NR_ptrace 117

/* kernel/sched.c */
#define __NR_sched_setparam 118
#define __NR_sched_setscheduler 119
#define __NR_sched_getscheduler 120
#define __NR_sched_getparam 121
#define __NR_sched_setaffinity 122
#define __NR_sched_getaffinity 123
#define __NR_sched_yield 124
#define __NR_sched_get_priority_max 125
#define __NR_sched_get_priority_min 126
#define __NR_sched_rr_get_interval 127

/* kernel/signal.c */
#define __NR_restart_syscall 128
#define __NR_kill 129
#define __NR_tkill 130
#define __NR_tgkill 131
#define __NR_sigaltstack 132
#define __NR_rt_sigsuspend 133
#define __NR_rt_sigaction 134
#define __NR_rt_sigprocmask 135
#define __NR_rt_sigpending 136
#define __NR_rt_sigtimedwait 137
#define __NR_rt_sigqueueinfo 138
#define __NR_rt_sigreturn 139

/* kernel/sys.c */
#define __NR_setpriority 140
#define __NR_getpriority 141
#define __NR_reboot 142
#define __NR_setregid 143
#define __NR_setgid 144
#define __NR_setreuid 145
#define __NR_setuid 146
#define __NR_setresuid 147
#define __NR_getresuid 148
#define __NR_setresgid 149
#define __NR_getresgid 150
#define __NR_setfsuid 151
#define __NR_setfsgid 152
#define __NR_times 153
#define __NR_setpgid 154
#define __NR_getpgid 155
#define __NR_getsid 156
#define __NR_setsid 157
#define __NR_getgroups 158
#define __NR_setgroups 159
#define __NR_uname 160
#define __NR_sethostname 161
#define __NR_setdomainname 162
#define __NR_getrlimit 163
#define __NR_setrlimit 164
#define __NR_getrusage 165
#define __NR_umask 166
#define __NR_prctl 167
#define __NR_getcpu 168

/* kernel/time.c */
#define __NR_gettimeofday 169

#define __NR_settimeofday 170
#define __NR_adjtimex 171

/* kernel/timer.c */
#define __NR_getpid 172
#define __NR_getppid 173
#define __NR_getuid 174
#define __NR_geteuid 175
#define __NR_getgid 176
#define __NR_getpgrp __NR_getgid
#define __NR_getegid 177
#define __NR_gettid 178
#define __NR_sysinfo 179

/* ipc/mqueue.c */
#define __NR_mq_open 180
#define __NR_mq_unlink 181
#define __NR_mq_timedsend 182
#define __NR_mq_timedreceive 183
#define __NR_mq_notify 184
#define __NR_mq_getsetattr 185

/* ipc/msg.c */
#define __NR_msgget 186
#define __NR_msgctl 187
#define __NR_msgrcv 188
#define __NR_msgsnd 189

/* ipc/sem.c */
#define __NR_semget 190
#define __NR_semctl 191
#define __NR_semtimedop 192
#define __NR_semop 193

/* ipc/shm.c */
#define __NR_shmget 194
#define __NR_shmctl 195
#define __NR_shmat 196
#define __NR_shmdt 197

/* net/socket.c */
#define __NR_socket 198
#define __NR_socketpair 199
#define __NR_bind 200
#define __NR_listen 201
#define __NR_accept 202
#define __NR_connect 203
#define __NR_getsockname 204
#define __NR_getpeername 205
#define __NR_sendto 206
#define __NR_recvfrom 207
#define __NR_setsockopt 208
#define __NR_getsockopt 209
#define __NR_shutdown 210
#define __NR_sendmsg 211
#define __NR_recvmsg 212

/* mm/filemap.c */
#define __NR_readahead 213

/* mm/nommu.c, also with MMU */
#define __NR_brk 214
#define __NR_munmap 215
#define __NR_mremap 216

/* security/keys/keyctl.c */
#define __NR_add_key 217
#define __NR_request_key 218
#define __NR_keyctl 219

/* arch/example/kernel/sys_example.c */
#define __NR_clone 220
#define __NR_fork  __NR_clone
#define __NR_execve 221
#define __NR_mmap  222

/* mm/fadvise.c */
#define __NR3264_fadvise64 223

/* mm/, CONFIG_MMU only */

#define __NR_swapon 224
#define __NR_swapoff 225
#define __NR_mprotect 226
#define __NR_msync 227
#define __NR_mlock 228
#define __NR_munlock 229
#define __NR_mlockall 230
#define __NR_munlockall 231
#define __NR_mincore 232
#define __NR_madvise 233
#define __NR_remap_file_pages 234
#define __NR_mbind 235
#define __NR_get_mempolicy 236
#define __NR_set_mempolicy 237
#define __NR_migrate_pages 238
#define __NR_move_pages 239
#define __NR_rt_tgsigqueueinfo 240
#define __NR_perf_event_open 241
#define __NR_accept4 242
#define __NR_recvmmsg 243

/*
 * Architectures may provide up to 16 syscalls of their own
 * starting with this value.
 */
#define __NR_arch_specific_syscall 244
#define __NR_cacheflush 245
#define __NR_set_dataplane 246
#define __NR_wait4 260
#define __NR_prlimit64 261
#define __NR_fanotify_init 262
#define __NR_fanotify_mark 263
#define __NR_syscalls 264

#endif /* __VKI_SCNUMS_TILEGX_LINUX_H */

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
