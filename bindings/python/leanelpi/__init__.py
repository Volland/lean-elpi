"""Python bindings for LeanElpi: the ELPI dialect of λProlog, running in Lean 4.

    >>> from leanelpi import Program
    >>> p = Program("pred app i:list int, i:list int, o:list int.\\n"
    ...             "app [] L L.\\napp [X|Xs] L [X|R] :- app Xs L R.")
    >>> p.first("app [1,2] [3] R")
    {'R': '[1, 2, 3]'}

Bindings come back as the strings ELPI prints. The engine lives in `libleanelpi`
(`scripts/build-ffi.sh`); it is found through `$LEANELPI_LIB`, next to this package, or in
`dist/` of a source checkout.
"""

from __future__ import annotations

import ctypes
import json
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterator

__all__ = ["Program", "Solution", "ElpiError", "version"]

_INVALID = 2**64 - 1


class ElpiError(Exception):
    """A parse, type or runtime error reported by the engine."""


def _candidates() -> Iterator[Path]:
    ext = "dylib" if sys.platform == "darwin" else "dll" if sys.platform == "win32" else "so"
    name = f"libleanelpi.{ext}"
    if env := os.environ.get("LEANELPI_LIB"):
        yield Path(env)
    here = Path(__file__).resolve().parent
    yield here / name
    for up in here.parents:
        yield up / "dist" / name


def _load() -> ctypes.CDLL:
    tried = []
    for path in _candidates():
        tried.append(str(path))
        if path.is_file():
            lib = ctypes.CDLL(str(path))
            break
    else:
        raise ImportError(
            "libleanelpi not found; run scripts/build-ffi.sh or set LEANELPI_LIB. Tried:\n  "
            + "\n  ".join(tried)
        )
    c_err = ctypes.POINTER(ctypes.c_char_p)
    lib.leanelpi_init.argtypes = [c_err]
    lib.leanelpi_init.restype = ctypes.c_int
    lib.leanelpi_version.restype = ctypes.c_char_p
    lib.leanelpi_load.argtypes = [ctypes.c_char_p, c_err]
    lib.leanelpi_load.restype = ctypes.c_uint64
    lib.leanelpi_assert.argtypes = [ctypes.c_uint64, ctypes.c_char_p, c_err]
    lib.leanelpi_assert.restype = ctypes.c_uint64
    lib.leanelpi_free.argtypes = [ctypes.c_uint64]
    lib.leanelpi_free.restype = None
    # Raw pointers, so the library's own allocation can be released with leanelpi_free_string.
    lib.leanelpi_solve.argtypes = [
        ctypes.c_uint64, ctypes.c_char_p, ctypes.c_uint64, ctypes.c_uint64, c_err]
    lib.leanelpi_solve.restype = ctypes.c_void_p
    lib.leanelpi_free_string.argtypes = [ctypes.c_void_p]
    lib.leanelpi_free_string.restype = None
    return lib


_lib: ctypes.CDLL | None = None


def _ffi() -> ctypes.CDLL:
    global _lib
    if _lib is None:
        lib = _load()
        err = ctypes.c_char_p()
        if lib.leanelpi_init(ctypes.byref(err)) != 0:
            raise ElpiError(_take(lib, err) or "cannot start the Lean runtime")
        _lib = lib
    return _lib


def _take(lib: ctypes.CDLL, err: ctypes.c_char_p) -> str | None:
    """Read and release an error string written by the library."""
    if not err:
        return None
    addr = ctypes.cast(err, ctypes.c_void_p)
    msg = err.value.decode("utf-8", "replace")  # type: ignore[union-attr]
    lib.leanelpi_free_string(addr)
    return msg


def version() -> str:
    """The version of the loaded engine."""
    return _ffi().leanelpi_version().decode()


@dataclass(frozen=True)
class Solution:
    """One answer: the query variables' values (as printed by ELPI) and suspended constraints."""

    bindings: dict[str, str]
    constraints: list[str] = field(default_factory=list)

    def __getitem__(self, name: str) -> str:
        return self.bindings[name]


# @tg: implements:: [[openspec:language-bindings#Python binding]]
class Program:
    """A compiled ELPI program. Programs are immutable: `assert_clause` returns a new one."""

    def __init__(self, source: str = "", *, _handle: int | None = None) -> None:
        lib = _ffi()
        if _handle is None:
            err = ctypes.c_char_p()
            _handle = lib.leanelpi_load(source.encode(), ctypes.byref(err))
            if _handle == _INVALID:
                raise ElpiError(_take(lib, err) or "load failed")
        self._handle: int | None = _handle

    def _live(self) -> int:
        if self._handle is None:
            raise ValueError("program is closed")
        return self._handle

    def assert_clause(self, clause: str) -> "Program":
        """A new program with `clause` added; this program is unchanged."""
        lib = _ffi()
        err = ctypes.c_char_p()
        h = lib.leanelpi_assert(self._live(), clause.encode(), ctypes.byref(err))
        if h == _INVALID:
            raise ElpiError(_take(lib, err) or "assert failed")
        return Program(_handle=h)

    def solve(self, query: str, *, limit: int | None = None, fuel: int | None = None) -> list[Solution]:
        """Run `query` and return up to `limit` solutions (all when None).

        `fuel` bounds resolution steps; running out raises ElpiError."""
        return self.solve_all(query, limit=limit, fuel=fuel)[0]

    def solve_all(self, query: str, *, limit: int | None = None, fuel: int | None = None
                  ) -> tuple[list[Solution], bool]:
        """Like `solve`, and also whether the search was exhausted (False when `limit` cut it)."""
        lib = _ffi()
        err = ctypes.c_char_p()
        ptr = lib.leanelpi_solve(self._live(), query.encode(), limit or 0, fuel or 0,
                                 ctypes.byref(err))
        if not ptr:
            raise ElpiError(_take(lib, err) or "query failed")
        try:
            doc = json.loads(ctypes.string_at(ptr).decode("utf-8"))
        finally:
            lib.leanelpi_free_string(ptr)
        sols = [Solution(s["bindings"], s["constraints"]) for s in doc["solutions"]]
        return sols, doc["exhausted"]

    def first(self, query: str, *, fuel: int | None = None) -> dict[str, str] | None:
        """The bindings of the first solution, or None when the query fails."""
        sols = self.solve(query, limit=1, fuel=fuel)
        return sols[0].bindings if sols else None

    def ask(self, query: str, *, fuel: int | None = None) -> bool:
        """Whether the query has a solution."""
        return self.first(query, fuel=fuel) is not None

    def close(self) -> None:
        if self._handle is not None and _lib is not None:
            _lib.leanelpi_free(self._handle)
        self._handle = None

    def __enter__(self) -> "Program":
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()

    def __del__(self) -> None:
        try:
            self.close()
        except Exception:
            pass
