/* getpid_loop: R rounds of N raw getpid syscalls in a tight loop.
 *
 *   getpid_loop [N [R]]      defaults: N = 1000000, R = 3
 *
 * No libc: each iteration is one `syscall` instruction (rax = 39), so the
 * loop measures syscall entry, dispatch and return and nothing else. The
 * program prints one line before and one line after each round; a host-side
 * timestamper on the console stream measures the round from those lines.
 * The CLOCK_MONOTONIC delta it prints is the guest's own clock, which is
 * virtual under Detcore and so not wall time there.
 *
 * Static, freestanding, linked at 0x8000001000 so it also loads under Narf
 * (its user range starts at PML4[1]). Build with build.sh.
 */

typedef unsigned long u64;

static inline long sys3(long n, long a, long b, long c) {
    long ret;
    __asm__ volatile("syscall"
                     : "=a"(ret)
                     : "a"(n), "D"(a), "S"(b), "d"(c)
                     : "rcx", "r11", "memory");
    return ret;
}

static u64 len(const char *s) {
    u64 n = 0;
    while (s[n])
        n++;
    return n;
}

static void put(const char *s) { sys3(1, 1, (long)s, (long)len(s)); }

static char *fmt_u64(char *end, u64 v) {
    *--end = 0;
    do {
        *--end = (char)('0' + v % 10);
        v /= 10;
    } while (v);
    return end;
}

static u64 parse_u64(const char *s, u64 dflt) {
    u64 v = 0;
    if (!s || !*s)
        return dflt;
    for (; *s; s++) {
        if (*s < '0' || *s > '9')
            return dflt;
        v = v * 10 + (u64)(*s - '0');
    }
    return v;
}

struct ts {
    long sec, nsec;
};

static u64 mono_ns(void) {
    struct ts t;
    sys3(228, 1 /* CLOCK_MONOTONIC */, (long)&t, 0);
    return (u64)t.sec * 1000000000ul + (u64)t.nsec;
}

static void line(const char *a, u64 x, const char *b, u64 y, const char *c, u64 z) {
    char buf[3][24];
    put(a);
    put(fmt_u64(buf[0] + 24, x));
    put(b);
    put(fmt_u64(buf[1] + 24, y));
    put(c);
    put(fmt_u64(buf[2] + 24, z));
    put("\n");
}

void cmain(long *sp) {
    long argc = sp[0];
    char **argv = (char **)(sp + 1);
    u64 n = parse_u64(argc > 1 ? argv[1] : 0, 1000000);
    u64 r = parse_u64(argc > 2 ? argv[2] : 0, 3);
    line("getpid-loop argc=", (u64)argc, " N=", n, " R=", r);
    for (u64 i = 0; i < r; i++) {
        line("getpid-loop B round=", i, " N=", n, " pid=", (u64)sys3(39, 0, 0, 0));
        u64 t0 = mono_ns();
        long bad = 0;
        for (u64 k = 0; k < n; k++)
            bad |= sys3(39, 0, 0, 0) < 0;
        u64 t1 = mono_ns();
        line("getpid-loop E round=", i, " guest_mono_ns=", t1 - t0, " errors=", (u64)bad);
    }
    put("getpid-loop-done\n");
    sys3(231, 0, 0, 0);
    for (;;)
        ;
}

__asm__(".globl _start\n"
        "_start:\n"
        "  xor %ebp, %ebp\n"
        "  mov %rsp, %rdi\n"
        "  and $-16, %rsp\n"
        "  call cmain\n"
        "  ud2\n");
