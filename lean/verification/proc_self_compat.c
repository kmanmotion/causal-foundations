/* Runtime compatibility only. The workspace reports a process-local PID but
 * exposes its own executable through /proc/self/exe, not /proc/<getpid()>/exe.
 * Redirect ONLY that exact current-process path to its standard self alias.
 * No Lean code, kernel operation, declaration, or proof is changed.
 * Ordinary Linux environments do not need this file.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>

ssize_t readlink(const char *path, char *buffer, size_t size) {
    typedef ssize_t (*readlink_fn)(const char *, char *, size_t);
    readlink_fn original = (readlink_fn)dlsym(RTLD_NEXT, "readlink");
    if (!original) { errno = ENOSYS; return -1; }
    char own_exe[80];
    snprintf(own_exe, sizeof own_exe, "/proc/%ld/exe", (long)getpid());
    return original(strcmp(path, own_exe) == 0 ? "/proc/self/exe" : path,
                    buffer, size);
}
