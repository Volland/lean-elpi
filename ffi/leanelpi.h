/* LeanElpi C API. Strings are UTF-8, NUL-terminated. Every function that can fail
 * returns an error message through `err` (free it with leanelpi_free_string) and
 * signals failure with LEANELPI_INVALID or NULL. Programs are immutable values:
 * leanelpi_assert returns a new handle and leaves the old one valid.
 * Calls may come from any thread; a handle may be used from several threads. */
#ifndef LEANELPI_H
#define LEANELPI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define LEANELPI_INVALID ((uint64_t)-1)

/* Start the Lean runtime. Idempotent; must succeed before any other call. 0 on success. */
int leanelpi_init(char **err);

/* Library version, e.g. "0.4.1". The pointer is owned by the library. */
const char *leanelpi_version(void);

/* Compile an ELPI program text. */
uint64_t leanelpi_load(const char *src, char **err);

/* Add clauses to a program; returns a new handle. */
uint64_t leanelpi_assert(uint64_t program, const char *clause, char **err);

/* Release a handle. Unknown or already-freed handles are ignored. */
void leanelpi_free(uint64_t program);

/* Run a query; returns JSON text (free with leanelpi_free_string):
 *   {"solutions":[{"bindings":{"X":"42"},"terms":{"X":{"i":42}},"constraints":[]}],
 *    "exhausted":true,"fuelUsed":123}
 * limit = 0 means all solutions; fuel = 0 means the default budget. Running out of fuel
 * fails with an err message starting with "out of fuel". Calling a declared host
 * predicate here (there is no host) is an error.
 *
 * Term JSON tree ("terms", and host arguments and rows):
 *   {"c":"name"}              constant
 *   {"c":"name","a":[t,...]}  constant applied to arguments
 *   {"i":42} {"f":1.5} {"s":"text"}   integer, float, string
 *   {"v":"X"}                 unassigned variable (host arguments; also an unbound answer)
 *   {"o":"printed"}           anything else, printed (λ-terms, applied variables; output only) */
char *leanelpi_solve(uint64_t program, const char *query, uint64_t limit, uint64_t fuel,
                     char **err);

/* Host callback: name is the declared predicate, args_json a JSON array with one term per
 * argument (unbound variables as {"v":name}). Return a malloc'd JSON string that the library
 * frees with free(): {"rows":[[term,...],...]} where each row holds one term per OUTPUT-mode
 * argument in order, or {"error":"message"}. NULL means no rows (failure). */
typedef char *(*leanelpi_host_fn)(void *ctx, const char *name, const char *args_json);

/* Declare a host predicate from signature source, e.g. "pred tm.triple o:term, o:term, o:term, o:int."
 * (types declared by the program or by the signature text itself). Returns a new handle; the old stays valid. */
uint64_t leanelpi_declare(uint64_t program, const char *name, const char *sig_src, char **err);

/* Like leanelpi_solve, but every declared host predicate calls `host(ctx, ...)` synchronously on the
 * calling thread. Result JSON:
 * {"solutions":[{"bindings":{"X":"42"},"terms":{"X":{"i":42}},"constraints":[]}],"exhausted":true,"fuelUsed":123}
 * Running out of fuel fails with an err message starting with "out of fuel". */
char *leanelpi_solve_host(uint64_t program, const char *query, uint64_t limit, uint64_t fuel,
                          leanelpi_host_fn host, void *ctx, char **err);

void leanelpi_free_string(char *s);

#ifdef __cplusplus
}
#endif
#endif
