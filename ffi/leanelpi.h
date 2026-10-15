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

/* Library version, e.g. "0.2.0". The pointer is owned by the library. */
const char *leanelpi_version(void);

/* Compile an ELPI program text. */
uint64_t leanelpi_load(const char *src, char **err);

/* Add clauses to a program; returns a new handle. */
uint64_t leanelpi_assert(uint64_t program, const char *clause, char **err);

/* Release a handle. Unknown or already-freed handles are ignored. */
void leanelpi_free(uint64_t program);

/* Run a query; returns JSON text (free with leanelpi_free_string):
 *   {"solutions":[{"bindings":{"X":"42"},"constraints":[]}],"exhausted":true}
 * limit = 0 means all solutions; fuel = 0 means the default budget. */
char *leanelpi_solve(uint64_t program, const char *query, uint64_t limit, uint64_t fuel,
                     char **err);

void leanelpi_free_string(char *s);

#ifdef __cplusplus
}
#endif
#endif
