/* Linux process measurements without inheriting a Python-sized fork image.
 * bench/run_benchmark.py starts every run of the timing table through this launcher.
 *
 * Build: make build/benchmark_native   (cc -O2 -std=c11 benchmark_native.c)
 * Usage: benchmark_native STATS_JSON TIMEOUT_SECONDS CPU_OR_MINUS_ONE -- PROGRAM ARGS...
 *
 * A small native parent launches exactly one measured child.  wait4 supplies
 * the child's CPU times and maximum resident set; memory is never polled.
 * CLOCK_MONOTONIC spans fork through reap, including exec and target cleanup.
 * The target's stdout/stderr are inherited, and statistics go to a separate file.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <math.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static volatile sig_atomic_t interrupted;
static volatile sig_atomic_t child_group;

static void on_signal(int number)
{
    int saved_errno = errno;
    interrupted = number;
    if (child_group > 0) kill(-(pid_t)child_group, SIGKILL);
    errno = saved_errno;
}

static double tv_seconds(struct timeval value)
{
    return (double)value.tv_sec + (double)value.tv_usec / 1000000.0;
}

static double elapsed(struct timespec start, struct timespec end)
{
    return (double)(end.tv_sec - start.tv_sec) +
           (double)(end.tv_nsec - start.tv_nsec) / 1000000000.0;
}

int main(int argc, char **argv)
{
    struct sigaction action;
    struct itimerval timer = {{0, 0}, {0, 0}};
    struct timespec start, end;
    struct rusage usage;
    char *tail;
    double timeout;
    long cpu;
    int status, timed_out = 0, returncode;
    pid_t child, waited;
    FILE *report;

    if (argc < 6 || strcmp(argv[4], "--") != 0) {
        fprintf(stderr, "usage: %s STATS_JSON TIMEOUT_SECONDS CPU_OR_MINUS_ONE -- PROGRAM ARGS...\n", argv[0]);
        return 2;
    }
    errno = 0;
    timeout = strtod(argv[2], &tail);
    if (errno || *tail || !isfinite(timeout) || timeout < 0) {
        fprintf(stderr, "invalid timeout\n");
        return 2;
    }
    errno = 0;
    cpu = strtol(argv[3], &tail, 10);
    if (errno || *tail || cpu < -1 || cpu >= CPU_SETSIZE) {
        fprintf(stderr, "invalid CPU index\n");
        return 2;
    }
    memset(&action, 0, sizeof(action));
    action.sa_handler = on_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGALRM, &action, NULL) ||
        sigaction(SIGTERM, &action, NULL) ||
        sigaction(SIGINT, &action, NULL)) {
        perror("sigaction");
        return 2;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &start)) {
        perror("clock_gettime");
        return 2;
    }
    child = fork();
    if (child < 0) {
        perror("fork");
        return 2;
    }
    if (child == 0) {
        if (setpgid(0, 0)) {
            perror("setpgid");
            _exit(126);
        }
        if (cpu >= 0) {
            cpu_set_t affinity;
            CPU_ZERO(&affinity);
            CPU_SET(cpu, &affinity);
            if (sched_setaffinity(0, sizeof(affinity), &affinity)) {
                perror("sched_setaffinity");
                _exit(126);
            }
        }
        execvp(argv[5], argv + 5);
        perror("execvp");
        _exit(127);
    }
    /* The child also calls setpgid, so killing its group is race-safe. */
    if (setpgid(child, child) && errno != EACCES && errno != ESRCH) {
        perror("setpgid");
        kill(child, SIGKILL);
        waitpid(child, NULL, 0);
        return 2;
    }
    child_group = (sig_atomic_t)child;
    if (timeout > 0) {
        timer.it_value.tv_sec = (time_t)timeout;
        timer.it_value.tv_usec = (suseconds_t)((timeout - (double)timer.it_value.tv_sec) * 1000000.0);
        if (!timer.it_value.tv_sec && !timer.it_value.tv_usec)
            timer.it_value.tv_usec = 1;
        if (setitimer(ITIMER_REAL, &timer, NULL)) {
            perror("setitimer");
            kill(-child, SIGKILL);
            waitpid(child, NULL, 0);
            return 2;
        }
    }
    for (;;) {
        if (interrupted) {
            timed_out = interrupted == SIGALRM;
            kill(-child, SIGKILL);
        }
        waited = wait4(child, &status, 0, &usage);
        if (waited == child) break;
        if (waited < 0 && errno == EINTR) continue;
        perror("wait4");
        kill(-child, SIGKILL);
        waitpid(child, NULL, 0);
        return 2;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &end)) {
        perror("clock_gettime");
        return 2;
    }
    timer.it_value.tv_sec = timer.it_value.tv_usec = 0;
    setitimer(ITIMER_REAL, &timer, NULL);
    if (interrupted == SIGALRM) timed_out = 1;
    child_group = 0;
    returncode = WIFEXITED(status) ? WEXITSTATUS(status) : -WTERMSIG(status);
    report = fopen(argv[1], "w");
    if (!report) {
        perror("statistics file");
        return 2;
    }
    fprintf(report,
        "{\"measurement_backend\":\"linux-native-wait4\","
        "\"wall_seconds\":%.9f,\"returncode\":%d,\"timed_out\":%s,"
        "\"cpu_seconds\":%.9f,\"user_seconds\":%.9f,\"system_seconds\":%.9f,"
        "\"peak_working_set_bytes\":%llu,\"page_faults\":%ld,"
        "\"minor_page_faults\":%ld,\"major_page_faults\":%ld,"
        "\"voluntary_context_switches\":%ld,\"involuntary_context_switches\":%ld}\n",
        elapsed(start, end), returncode, timed_out ? "true" : "false",
        tv_seconds(usage.ru_utime) + tv_seconds(usage.ru_stime),
        tv_seconds(usage.ru_utime), tv_seconds(usage.ru_stime),
        (unsigned long long)usage.ru_maxrss * 1024ULL,
        usage.ru_minflt + usage.ru_majflt, usage.ru_minflt, usage.ru_majflt,
        usage.ru_nvcsw, usage.ru_nivcsw);
    if (fclose(report)) {
        perror("statistics file");
        return 2;
    }
    return 0;
}
