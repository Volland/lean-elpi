/* C shim over the @[export] functions of Elpi/Ffi.lean: starts the Lean runtime and
 * turns Lean IO results into plain C values. */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
#include "leanelpi.h"

extern void lean_initialize(void);
extern void lean_initialize_thread(void);
extern lean_object *lean_io_error_to_string(lean_object *err);
/* Lake mangles the package name "lean-elpi" into the module initializer's symbol. */
extern lean_object *initialize_lean_x2delpi_Elpi_Ffi(uint8_t builtin);
extern lean_object *leanelpi_ffi_load(lean_obj_arg src);
extern lean_object *leanelpi_ffi_assert(uint64_t h, lean_obj_arg clause);
extern lean_object *leanelpi_ffi_free(uint64_t h);
extern lean_object *leanelpi_ffi_solve(uint64_t h, lean_obj_arg q, uint64_t limit,
                                       uint64_t fuel);
extern lean_object *leanelpi_ffi_declare(uint64_t h, lean_obj_arg name, lean_obj_arg sig);
extern lean_object *leanelpi_ffi_solve_host(uint64_t h, lean_obj_arg q, uint64_t limit,
                                            uint64_t fuel, size_t fn, size_t ctx);
extern const lean_object *leanelpi_ffi_version;

static char *dup_cstr(const char *s) {
    size_t n = strlen(s) + 1;
    char *r = malloc(n);
    if (r) memcpy(r, s, n);
    return r;
}

static void set_err(char **err, const char *msg) {
    if (err) *err = dup_cstr(msg);
}

/* Move the error of a failed IO result into `err` and release the result. */
static void take_error(lean_object *res, char **err) {
    lean_object *e = lean_io_result_get_error(res);
    lean_inc(e);
    lean_object *s = lean_io_error_to_string(e);
    set_err(err, lean_string_cstr(s));
    lean_dec(s);
    lean_dec(res);
}

static _Thread_local int thread_ready = 0;
static void ensure_thread(void) {
    if (!thread_ready) {
        lean_initialize_thread();
        thread_ready = 1;
    }
}

static int started = 0;

int leanelpi_init(char **err) {
    if (started) return 0;
    lean_initialize();
    lean_init_task_manager();
    lean_object *res = initialize_lean_x2delpi_Elpi_Ffi(1);
    if (!lean_io_result_is_ok(res)) {
        take_error(res, err);
        return 1;
    }
    lean_dec(res);
    lean_io_mark_end_initialization();
    thread_ready = 1;
    started = 1;
    return 0;
}

const char *leanelpi_version(void) {
    static char *v = NULL;
    if (!v) {
        v = dup_cstr(lean_string_cstr((lean_object *)leanelpi_ffi_version));
    }
    return v;
}

uint64_t leanelpi_load(const char *src, char **err) {
    ensure_thread();
    lean_object *s = lean_mk_string(src);
    lean_object *res = leanelpi_ffi_load(s);
    if (!lean_io_result_is_ok(res)) { take_error(res, err); return LEANELPI_INVALID; }
    uint64_t h = lean_unbox_uint64(lean_io_result_get_value(res));
    lean_dec(res);
    return h;
}

uint64_t leanelpi_assert(uint64_t program, const char *clause, char **err) {
    ensure_thread();
    lean_object *s = lean_mk_string(clause);
    lean_object *res = leanelpi_ffi_assert(program, s);
    if (!lean_io_result_is_ok(res)) { take_error(res, err); return LEANELPI_INVALID; }
    uint64_t h = lean_unbox_uint64(lean_io_result_get_value(res));
    lean_dec(res);
    return h;
}

void leanelpi_free(uint64_t program) {
    ensure_thread();
    lean_object *res = leanelpi_ffi_free(program);
    lean_dec(res);
}

char *leanelpi_solve(uint64_t program, const char *query, uint64_t limit, uint64_t fuel,
                     char **err) {
    ensure_thread();
    lean_object *q = lean_mk_string(query);
    lean_object *res = leanelpi_ffi_solve(program, q, limit, fuel);
    if (!lean_io_result_is_ok(res)) { take_error(res, err); return NULL; }
    char *out = dup_cstr(lean_string_cstr(lean_io_result_get_value(res)));
    lean_dec(res);
    return out;
}

uint64_t leanelpi_declare(uint64_t program, const char *name, const char *sig_src, char **err) {
    ensure_thread();
    lean_object *n = lean_mk_string(name);
    lean_object *g = lean_mk_string(sig_src);
    lean_object *res = leanelpi_ffi_declare(program, n, g);
    if (!lean_io_result_is_ok(res)) { take_error(res, err); return LEANELPI_INVALID; }
    uint64_t h = lean_unbox_uint64(lean_io_result_get_value(res));
    lean_dec(res);
    return h;
}

/* Called from Lean (Elpi.Ffi.hostCall, @[extern "leanelpi_host_call"]): run the host
 * function and hand its answer back as `Option String`; the host's string is freed here. */
lean_object *leanelpi_host_call(size_t fn, size_t ctx, b_lean_obj_arg name, b_lean_obj_arg args) {
    leanelpi_host_fn host = (leanelpi_host_fn)fn;
    char *out = host((void *)ctx, lean_string_cstr(name), lean_string_cstr(args));
    if (!out) return lean_io_result_mk_ok(lean_box(0));
    lean_object *s = lean_mk_string(out);
    free(out);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, s);
    return lean_io_result_mk_ok(some);
}

char *leanelpi_solve_host(uint64_t program, const char *query, uint64_t limit, uint64_t fuel,
                          leanelpi_host_fn host, void *ctx, char **err) {
    ensure_thread();
    if (!host) { set_err(err, "leanelpi_solve_host: host function is NULL"); return NULL; }
    lean_object *q = lean_mk_string(query);
    lean_object *res = leanelpi_ffi_solve_host(program, q, limit, fuel, (size_t)host, (size_t)ctx);
    if (!lean_io_result_is_ok(res)) { take_error(res, err); return NULL; }
    char *out = dup_cstr(lean_string_cstr(lean_io_result_get_value(res)));
    lean_dec(res);
    return out;
}

void leanelpi_free_string(char *s) { free(s); }
