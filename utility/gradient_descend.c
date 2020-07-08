#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/time.h>
#include "gradient_descend.h"

#ifndef likely
#define likely(x) __builtin_expect(!!(x), 1)
#endif
#ifndef unlikely
#define unlikely(x) __builtin_expect(!!(x), 0)
#endif

#define ASSERT_OR_ABORT(x, mex)                                                \
    if (unlikely(!(x))) {                                                      \
        fprintf(stderr, "[gd ABORT] " mex "\n");                               \
        abort();                                                               \
    }

#define DEBUG_GRADIENT 0
#define DEBUG_PARTIAL_DERIVATIVE 0
#define DEBUG_DESCEND 0
#define DEBUG_MINIMIZE 0
#define DEBUG_DESC_TRANSF 0
#define ALLOW_RANDOM_RESTART 0
#define RESTART_SCORE 4

#define max(x, y) (x) > (y) ? (x) : (y)
#define min(x, y) (x) < (y) ? (x) : (y)

#define DEBUG_PRINTF(format, ...)                                              \
    if (DEBUG) {                                                               \
        fprintf(stderr, format, ##__VA_ARGS__);                                \
    }

#define GD_MOMENTUM_BETA 0.0L
#define GD_ESCAPE_RATIO 1.0L
#define MAX_EPOCH 1000
#define MAX_RANDOM_INPUT 0

#define WRAPPING_ADD_8(x, y) (uint8_t)((uint8_t)(x) + (uint8_t)(y))
#define WRAPPING_SUB_8(x, y) (uint8_t)((uint8_t)(x) - (uint8_t)(y))
#define STATIONARY 0
#define ASCENDING 1
#define DESCENDING 2

#define EXIT_ERROR 0xffff
#define EXIT_OK 1

static inline uint8_t saturating_add8(uint8_t a, uint8_t b)
{
    return (a > 0xFF - b) ? 0xFF : a + b;
}

static inline uint8_t saturating_sub8(uint8_t a, uint8_t b)
{
    return b > a ? 0 : a - b;
}

typedef struct gradient_el_t {
    uint64_t value;
    uint8_t  direction;
    double   pct;
} gradient_el_t;

#define RESEED_RNG 10000
static int             dev_urandom_fd = -1;
static unsigned        rand_cnt       = 1;
static inline unsigned UR(unsigned limit)
{
    if (!rand_cnt--) {
        unsigned seed[2];
        size_t   res = read(dev_urandom_fd, &seed, sizeof(seed));
        ASSERT_OR_ABORT(res == sizeof(seed), "read failed");
        srandom(seed[0]);
        rand_cnt = (RESEED_RNG / 2) + (seed[1] % RESEED_RNG);
    }
    return random() % limit;
}

static __attribute__((unused)) void debug_dump_vector(char* name, uint64_t* v,
                                                      uint32_t n)
{
    fprintf(stderr, "*** vector %s ***\n", name);
    unsigned j;
    for (j = 0; j < n; ++j) {
        fprintf(stderr, "-> v[%u]\t= 0x%016lx\n", j, v[j]);
    }
    fprintf(stderr, "*** end %s ***\n", name);
}

static int partial_derivative(gradient_el_t* out_grad_el,
                              uint64_t (*function)(uint64_t*, int*), int64_t f0,
                              uint64_t* x0, uint32_t i)
{
    int      should_exit;
    uint64_t original_val = x0[i];
    x0[i]                 = original_val + 1;
    int64_t f_plus        = (int64_t)function(x0, &should_exit);
    if (unlikely(should_exit))
        return EXIT_ERROR;
    x0[i]           = original_val - 1;
    int64_t f_minus = (int64_t)function(x0, &should_exit);
    if (unlikely(should_exit))
        return EXIT_ERROR;
    x0[i] = original_val;

#if DEBUG_PARTIAL_DERIVATIVE
    fprintf(stderr, ">>> PARTIAL DERIVATIVE\n");
    fprintf(stderr,
            "i:       %u\n"
            "x0[i]:   0x%016lx\n"
            "f0:      0x%016lx [%ld]\n"
            "f_plus:  0x%016lx [%ld]\n"
            "f_minus: 0x%016lx [%ld]\n",
            i, x0[i], f0, f0, f_plus, f_plus, f_minus, f_minus);
    fprintf(stderr, "<<< END PARTIAL DERIVATIVE\n");
#endif

    if (f0 <= f_minus && f0 <= f_plus) {
        out_grad_el->value     = 0;
        out_grad_el->direction = STATIONARY;
        return EXIT_OK; // no gradient
    }
    if (f_plus < f0 && f0 <= f_minus) {
        out_grad_el->value     = f0 - f_plus;
        out_grad_el->direction = DESCENDING;
        return EXIT_OK;
    }
    if (f_minus < f0 && f0 <= f_plus) {
        out_grad_el->value     = f0 - f_minus;
        out_grad_el->direction = ASCENDING;
        return EXIT_OK;
    }
    if (f_minus < f0 && f_plus < f0 && f_minus < f_plus) {
        out_grad_el->value     = f0 - f_minus;
        out_grad_el->direction = ASCENDING;
        return EXIT_OK;
    }
    if (f_minus < f0 && f_plus < f0 && f_minus >= f_plus) {
        out_grad_el->value     = f0 - f_plus;
        out_grad_el->direction = DESCENDING;
        return EXIT_OK;
    }
    ASSERT_OR_ABORT(0, "partial_derivative - should be unreachable");
}

static int compute_gradient(gradient_el_t* out_grad,
                            uint64_t (*function)(uint64_t*, int*), int64_t f0,
                            uint64_t* x0, uint32_t n)
{
    uint32_t i;
    for (i = 0; i < n; ++i) {
        int res = partial_derivative(&out_grad[i], function, f0, x0, i);
        if (unlikely(res == EXIT_ERROR))
            return EXIT_ERROR;
        out_grad[i].pct = 0.0L;
    }
#if DEBUG_GRADIENT
    fprintf(stderr, ">>> GRADIENT RAW\n");
    for (i = 0; i < n; ++i) {
        if (i > 0)
            fprintf(stderr, "\n");
        fprintf(stderr,
                "  grad[%d].value     = 0x%016lx\n"
                "  grad[%d].direction = %u\n",
                i, out_grad[i].value, i, out_grad[i].direction);
    }
    fprintf(stderr, "<<< END GRADIENT RAW\n");
#endif
    return EXIT_OK;
}

static uint64_t max_gradient(gradient_el_t* grad, uint32_t size)
{
    uint32_t i;
    uint64_t max = 0;
    for (i = 0; i < size; ++i)
        if (grad[i].value > max)
            max = grad[i].value;
    return max;
}

static void normalize_gradient(gradient_el_t* grad, uint32_t size)
{
    uint64_t max = max_gradient(grad, size);

    uint32_t i;
    for (i = 0; i < size; ++i)
        grad[i].pct = GD_MOMENTUM_BETA * grad[i].pct +
                      (1.0L - GD_MOMENTUM_BETA) * ((double)grad[i].value) / max;

#if DEBUG_GRADIENT
    fprintf(stderr, "  gradient:\n");
    unsigned j;
    for (j = 0; j < size; ++j)
        fprintf(stderr,
                "    grad[%u].value     = 0x%016lx\n"
                "    grad[%u].direction = %s\n"
                "    grad[%u].pct       = %.08lf\n\n",
                j, grad[j].value, j,
                grad[j].direction == ASCENDING
                    ? "ASCENDING"
                    : (grad[j].direction == DESCENDING ? "DESCENDING"
                                                       : "STATIONARY"),
                j, grad[j].pct);
#endif
}

static void compute_delta_all(uint64_t* x, gradient_el_t* grad, uint64_t step,
                              uint32_t n, uint8_t descending)
{
    uint32_t i;
    for (i = 0; i < n; ++i) {
        if (descending && grad[i].direction == ASCENDING)
            x[i] = x[i] - grad[i].pct * step;
        else if (descending && grad[i].direction == DESCENDING)
            x[i] = x[i] + grad[i].pct * step;
        else if (!descending && grad[i].direction == ASCENDING)
            x[i] = x[i] + grad[i].pct * step;
        else if (!descending && grad[i].direction == DESCENDING)
            x[i] = x[i] - grad[i].pct * step;
    }
}

static int descend(uint64_t (*function)(uint64_t*, int*), gradient_el_t* grad,
                   uint64_t* x0, int64_t f0, uint64_t* out_x, int64_t* out_f,
                   uint32_t n)
{
#if DEBUG_DESCEND
    fprintf(stderr, ">>> DESCEND\n");
#endif
    int       should_exit;
    int       res    = EXIT_OK;
    int64_t   f_prev = f0;
    int64_t   f_next = f0;
    uint64_t* x_prev = (uint64_t*)malloc(sizeof(uint64_t) * n);
    uint64_t* x_next = out_x;
    memcpy(x_next, x0, sizeof(uint64_t) * n);

#if ALLOW_RANDOM_RESTART
    int64_t   f0_tmp = f_prev;
    uint64_t* x0_tmp = (uint64_t*)malloc(sizeof(uint64_t) * n);
    memcpy(x0_tmp, x_next, sizeof(uint64_t) * n);
    int k = 0;
    while (k++ < n * RESTART_SCORE) {
        fprintf(stderr, "trying restart...\n");
        switch (UR(4)) {
            case 0:
                x0_tmp[UR(n)] ^= UR(256) + 1;
                break;
            case 1:
                x0_tmp[UR(n)] ^= (UR(256) + 1) << 8;
                break;
            case 2:
                x0_tmp[UR(n)] ^= (UR(256) + 1) << 16;
                break;
            case 3:
                x0_tmp[UR(n)] ^= (UR(256) + 1) << 24;
                break;
        }
        int64_t f_val = function(x0_tmp, &should_exit);
        if (unlikely(should_exit)) {
            res = EXIT_ERROR;
            goto OUT;
        }
        if (f_val < f0_tmp) {
            f0_tmp = f_val;
            f_prev = f_next = f0_tmp;
            memcpy(x_next, x0_tmp, sizeof(uint64_t) * n);
            fprintf(stderr, "random restart effective!\n");
        } else {
            memcpy(x0_tmp, x_next, sizeof(uint64_t) * n);
        }
    }
    free(x0_tmp);
#endif

    uint64_t step = 1;
    while (1) {
        memcpy(x_prev, x_next, sizeof(uint64_t) * n);
        compute_delta_all(x_next, grad, step, n, 1);

        f_next = function(x_next, &should_exit);
        if (unlikely(should_exit)) {
            res = EXIT_ERROR;
            goto OUT;
        }
#if DEBUG_DESCEND
        fprintf(stderr,
                "f_prev: %lx\n"
                "f_next: %lx\n",
                f_prev, f_next);
#endif
        if (f_next >= f_prev)
            break;

        step *= 2;
        f_prev = f_next;
    }
    memcpy(x_next, x_prev, sizeof(uint64_t) * n);

    if (n == 1)
        goto OUT;

    uint32_t delta_idx = 0;
    while (delta_idx < n && grad[delta_idx].pct < 0.01)
        delta_idx++;

    if (delta_idx >= n)
        goto OUT;

    step = 1;
    while (1) {
        while (1) {
            memcpy(x_prev, x_next, sizeof(uint64_t) * n);

            uint64_t movement = grad[delta_idx].pct * step;
            if (grad[delta_idx].direction == ASCENDING)
                x_next[delta_idx] = x_next[delta_idx] - movement;
            else if (grad[delta_idx].direction == DESCENDING)
                x_next[delta_idx] = x_next[delta_idx] + movement;
            else {
                ASSERT_OR_ABORT(0, "descend - should be unreachable");
            }

            f_next = function(x_next, &should_exit);
            if (unlikely(should_exit)) {
                res = EXIT_ERROR;
                goto OUT;
            }
#if DEBUG_DESCEND
            fprintf(stderr,
                    "delta_idx: %u\n"
                    "  f_prev: 0x%016lx\n"
                    "  f_next: 0x%016lx\n",
                    delta_idx, f_prev, f_next);
#endif
            if (f_next >= f_prev)
                break;

            step *= 2;
            f_prev = f_next;
        }
        memcpy(x_next, x_prev, sizeof(uint64_t) * n);

        delta_idx++;
        while (delta_idx < n && grad[delta_idx].pct < 0.01)
            delta_idx++;

        if (delta_idx >= n)
            goto OUT;
        step = 1;
    }

OUT:
#if DEBUG_DESCEND
    fprintf(stderr, "<<< END DESCEND\n");
#endif
    *out_f = f_prev;
    free(x_prev);
    return res;
}

int gd_minimize(uint64_t (*function)(uint64_t*, int*), uint64_t* x0,
                uint64_t* out_x_min, uint64_t* out_f_min, uint32_t n)
{
#if DEBUG_MINIMIZE
    uint32_t j;
    fprintf(stderr, ">>> MINIMIZE\n");
    for (j = 0; j < n; ++j) {
        fprintf(stderr, "x0[%u]: 0x%016lx\n", j, x0[j]);
    }
    int dummy;
    fprintf(stderr, "f0: 0x%016lx\n", function(x0, &dummy));

#endif
    int            res = EXIT_OK;
    int            should_exit;
    gradient_el_t* gradient = (gradient_el_t*)malloc(sizeof(gradient_el_t) * n);

    uint64_t* x_prev = (uint64_t*)malloc(sizeof(uint64_t) * n);
    uint64_t* x_next = out_x_min;
    memcpy(x_next, x0, n * sizeof(uint64_t));

    int64_t f_prev = (int64_t)function(x0, &should_exit);
    if (unlikely(should_exit)) {
        res = EXIT_ERROR;
        goto OUT;
    }

    int64_t f_next = f_prev;

    uint32_t epoch = 0;
    while (epoch < MAX_EPOCH) {
        memcpy(x_prev, x_next, n * sizeof(uint64_t));
        f_prev = f_next;

        int grad_res = compute_gradient(gradient, function, f_prev, x_prev, n);
        if (unlikely(grad_res == EXIT_ERROR)) {
            res = EXIT_ERROR;
            goto OUT;
        }

        uint32_t i        = 0;
        uint64_t max_grad = max_gradient(gradient, n);
        while (max_grad == 0 && i++ < MAX_RANDOM_INPUT) {
            x_prev[UR(n)] ^= UR(256);
            f_prev = function(x0, &should_exit);
            if (unlikely(should_exit)) {
                res = EXIT_ERROR;
                goto OUT;
            }

            grad_res = compute_gradient(gradient, function, f_prev, x_prev, n);
            if (unlikely(grad_res == EXIT_ERROR)) {
                res = EXIT_ERROR;
                goto OUT;
            }
            max_grad = max_gradient(gradient, n);
        }
        if (i > MAX_RANDOM_INPUT)
            break;

        normalize_gradient(gradient, n);

#if DEBUG_MINIMIZE
        fprintf(stderr, "\nepoch: %u\n", epoch);
        fprintf(stderr, "  gradient:\n");
        for (j = 0; j < n; ++j)
            fprintf(stderr,
                    "    grad[%u].value     = 0x%016lx\n"
                    "    grad[%u].direction = %s\n"
                    "    grad[%u].pct       = %.08lf\n\n",
                    j, gradient[j].value, j,
                    gradient[j].direction == ASCENDING
                        ? "ASCENDING"
                        : (gradient[j].direction == DESCENDING ? "DESCENDING"
                                                               : "STATIONARY"),
                    j, gradient[j].pct);
#endif

        int descend_res =
            descend(function, gradient, x_prev, f_prev, x_next, &f_next, n);
        if (unlikely(descend_res == EXIT_ERROR)) {
            res = EXIT_ERROR;
            goto OUT;
        }
        if (f_prev == f_next)
            break;

#if DEBUG_MINIMIZE
        fprintf(stderr, "  x_prev:\n");
        for (j = 0; j < n; ++j)
            fprintf(stderr, "    x_prev[%u] = 0x%016lx\n", j, x_prev[j]);
        fprintf(stderr, "  f_prev:\n    %016lx\n", f_prev);
        fprintf(stderr, "  x_next:\n");
        for (j = 0; j < n; ++j)
            fprintf(stderr, "    x_next[%u] = 0x%016lx\n", j, x_next[j]);
        fprintf(stderr, "  f_next:\n    %016lx\n", f_next);
#endif
        epoch++;
    }

    *out_f_min = (uint64_t)f_next;
OUT:
    free(gradient);
    free(x_prev);

#if DEBUG_MINIMIZE
    fprintf(stderr, "<<< END MINIMIZE\n");
#endif
    return res;
}

static gradient_el_t* __tmp_gradient;
static unsigned       __tmp_gradient_size = 0;
static void           init_tmp_gradient(uint32_t n)
{
    if (__tmp_gradient_size < n) {
        __tmp_gradient = realloc(__tmp_gradient, n * sizeof(gradient_el_t));
        __tmp_gradient_size = n;
    }
}

int gd_descend_transf(uint64_t (*function)(uint64_t*, int*), uint64_t* x0,
                      uint64_t* out_x, uint64_t* out_f, uint32_t n)
{
#if DEBUG_DESC_TRANSF
    debug_dump_vector("x0 (desc)", x0, n);
#endif

    int should_exit;
    init_tmp_gradient(n);
    gradient_el_t* gradient = __tmp_gradient;

    int64_t f0 = function(x0, &should_exit);
    if (unlikely(should_exit))
        return EXIT_ERROR;

    int grad_res = compute_gradient(gradient, function, f0, x0, n);
    if (unlikely(grad_res == EXIT_ERROR))
        return EXIT_ERROR;
    if (max_gradient(gradient, n) == 0) {
        // we reached a min
        return 1;
    }
    normalize_gradient(gradient, n);

    int descend_res =
        descend(function, gradient, x0, f0, out_x, (int64_t*)out_f, n);
    if (unlikely(descend_res == EXIT_ERROR))
        return EXIT_ERROR;

#if DEBUG_DESC_TRANSF
    debug_dump_vector("out_x (desc)", out_x, n);
#endif
    return 0;
}

int gd_max_gradient(uint64_t (*function)(uint64_t*, int*), uint64_t* x0,
                    uint32_t n, uint64_t* v)
{
    init_tmp_gradient(n);

    int     should_exit;
    int64_t f0 = function(x0, &should_exit);
    if (unlikely(should_exit))
        return 0;

    gradient_el_t* gradient = __tmp_gradient;
    int            grad_res = compute_gradient(gradient, function, f0, x0, n);
    if (unlikely(grad_res == EXIT_ERROR))
        return 0;

    *v = max_gradient(gradient, n);
    return 1;
}

void gd_init()
{
    dev_urandom_fd = open("/dev/urandom", O_RDONLY);
    if (dev_urandom_fd < 0)
        ASSERT_OR_ABORT(0, "Unable to open /dev/urandom");

    __tmp_gradient      = (gradient_el_t*)malloc(sizeof(gradient_el_t) * 10);
    __tmp_gradient_size = 10;
}

void gd_free()
{
    close(dev_urandom_fd);
    free(__tmp_gradient);
    __tmp_gradient_size = 0;
    __tmp_gradient      = NULL;
}
