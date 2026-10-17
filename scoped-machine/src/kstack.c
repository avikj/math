/* kstack.c — see kstack.h. */
#define _GNU_SOURCE
#include "kstack.h"
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/mman.h>
#include <ucontext.h>

#if defined(__SANITIZE_ADDRESS__)
void __sanitizer_start_switch_fiber(void **fake_stack_save, const void *bottom, size_t size);
void __sanitizer_finish_switch_fiber(void *fake_stack_save, const void **bottom_old, size_t *size_old);
#endif
#if defined(__SANITIZE_THREAD__)
void *__tsan_get_current_fiber(void);
void *__tsan_create_fiber(unsigned flags);
void __tsan_destroy_fiber(void *fiber);
void __tsan_switch_to_fiber(void *fiber, unsigned flags);
#endif

static __thread char *seg_lo;          /* lowest usable address of the current segment */
static __thread size_t nseg;
static __thread void (*run_fn)(void *); static __thread void *run_arg;
static __thread ucontext_t *ret_ctx;
#if defined(__SANITIZE_THREAD__)
static __thread void *ret_fiber;
#endif
#if defined(__SANITIZE_ADDRESS__)
static __thread const void *asan_ret_bottom; static __thread size_t asan_ret_size;
#endif

static void init_bounds(void) {
    pthread_attr_t a; void *addr = NULL; size_t size = 0;
    if (pthread_getattr_np(pthread_self(), &a) == 0) { pthread_attr_getstack(&a, &addr, &size); pthread_attr_destroy(&a); }
    seg_lo = addr ? (char *)addr + 4096 : NULL;   /* one guard page of slack */
}
bool kstack_low(void) {
    char *sp = (char *)__builtin_frame_address(0);   /* the native stack pointer (a sanitizer's fake stack is not consulted) */
    if (!seg_lo) init_bounds();
    if (!seg_lo) return false;
    return sp < seg_lo || (size_t)(sp - seg_lo) < KSTACK_RESERVE;
}
size_t kstack_segments(void) { return nseg; }

static void trampoline(void) {
#if defined(__SANITIZE_ADDRESS__)
    __sanitizer_finish_switch_fiber(NULL, &asan_ret_bottom, &asan_ret_size);
#endif
    run_fn(run_arg);
    /* back to the caller's segment (uc_link is not used: the sanitizer
     * switch has to be announced before the final switch) */
#if defined(__SANITIZE_ADDRESS__)
    __sanitizer_start_switch_fiber(NULL, asan_ret_bottom, asan_ret_size);
#endif
#if defined(__SANITIZE_THREAD__)
    __tsan_switch_to_fiber(ret_fiber, 0);
#endif
    setcontext(ret_ctx);
}

void kstack_run(void (*fn)(void *), void *arg) {
    char *seg = mmap(NULL, KSTACK_SEG, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (seg == MAP_FAILED) { fprintf(stderr, "fatal: kstack: the host could not supply a stack segment\n"); abort(); }
    ucontext_t here, there;
    getcontext(&there);
    there.uc_stack.ss_sp = seg; there.uc_stack.ss_size = KSTACK_SEG; there.uc_link = NULL;
    makecontext(&there, trampoline, 0);
    /* save the per-thread switch state of an enclosing segment call */
    char *lo_save = seg_lo; void (*fn_save)(void *) = run_fn; void *arg_save = run_arg; ucontext_t *ret_save = ret_ctx;
#if defined(__SANITIZE_THREAD__)
    void *fiber_save = ret_fiber; ret_fiber = __tsan_get_current_fiber(); void *fiber = __tsan_create_fiber(0);
#endif
#if defined(__SANITIZE_ADDRESS__)
    const void *ab_save = asan_ret_bottom; size_t as_save = asan_ret_size; void *fake = NULL;
#endif
    run_fn = fn; run_arg = arg; ret_ctx = &here; seg_lo = seg + 4096; nseg++;
#if defined(__SANITIZE_ADDRESS__)
    __sanitizer_start_switch_fiber(&fake, seg, KSTACK_SEG);
#endif
#if defined(__SANITIZE_THREAD__)
    __tsan_switch_to_fiber(fiber, 0);
#endif
    swapcontext(&here, &there);
#if defined(__SANITIZE_ADDRESS__)
    __sanitizer_finish_switch_fiber(fake, NULL, NULL);
    asan_ret_bottom = ab_save; asan_ret_size = as_save;
#endif
#if defined(__SANITIZE_THREAD__)
    __tsan_destroy_fiber(fiber); ret_fiber = fiber_save;
#endif
    seg_lo = lo_save; run_fn = fn_save; run_arg = arg_save; ret_ctx = ret_save;
    munmap(seg, KSTACK_SEG);
}
