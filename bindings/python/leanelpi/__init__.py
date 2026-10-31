"""Python bindings for LeanElpi: the ELPI dialect of λProlog, running in Lean 4.

    >>> from leanelpi import Program
    >>> p = Program("pred app i:list int, i:list int, o:list int.\\n"
    ...             "app [] L L.\\napp [X|Xs] L [X|R] :- app Xs L R.")
    >>> p.first("app [1,2] [3] R")
    {'R': '[1, 2, 3]'}

Bindings come back as the strings ELPI prints (`Solution.bindings`) and as Python values
(`Solution.terms`). A predicate declared with `Program.declare` is answered by Python code
during `Program.solve_host`. The engine lives in `libleanelpi` (`scripts/build-ffi.sh`); it
is found through `$LEANELPI_LIB`, next to this package, or in `dist/` of a source checkout.
"""

from __future__ import annotations

import ctypes
import json
import math
import os
import re
import sys
from collections.abc import Mapping as _MappingABC
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, Iterator, List, Mapping, Optional, Tuple, Union

__all__ = [
    "Program", "Solution", "HostRun", "ElpiError", "version",
    "Const", "App", "Var", "Opaque", "Term", "Host",
]

_INVALID = 2**64 - 1


class ElpiError(Exception):
    """A parse, type or runtime error reported by the engine, or an error raised by a host
    predicate (then `__cause__` is the original exception)."""

    @property
    def out_of_fuel(self) -> bool:
        """Whether the run stopped because its fuel budget ran out."""
        return str(self).startswith("out of fuel")


def _candidates() -> Iterator[Path]:
    ext = "dylib" if sys.platform == "darwin" else "dll" if sys.platform == "win32" else "so"
    name = f"libleanelpi.{ext}"
    if env := os.environ.get("LEANELPI_LIB"):
        yield Path(env)
    here = Path(__file__).resolve().parent
    yield here / name
    for up in here.parents:
        yield up / "dist" / name


# char *(*leanelpi_host_fn)(void *ctx, const char *name, const char *args_json). The result is
# a raw pointer (c_void_p), not c_char_p: it must be memory from the C allocator, which the
# library releases with free(); a c_char_p result would point into a Python object.
_HOST_FN = ctypes.CFUNCTYPE(ctypes.c_void_p, ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p)


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
    if hasattr(lib, "leanelpi_declare"):  # 0.4.0 and later
        lib.leanelpi_declare.argtypes = [ctypes.c_uint64, ctypes.c_char_p, ctypes.c_char_p, c_err]
        lib.leanelpi_declare.restype = ctypes.c_uint64
        lib.leanelpi_solve_host.argtypes = [
            ctypes.c_uint64, ctypes.c_char_p, ctypes.c_uint64, ctypes.c_uint64, _HOST_FN,
            ctypes.c_void_p, c_err]
        lib.leanelpi_solve_host.restype = ctypes.c_void_p
    return lib


_lib: ctypes.CDLL | None = None
_malloc: Any = None


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


def _c_malloc() -> Any:
    """The `malloc` that pairs with the `free()` the library calls on a host answer: looked up
    through the library's own handle (dlsym searches its dependencies, so this is the C
    runtime it links), falling back to the process's."""
    global _malloc
    if _malloc is None:
        try:
            m = _ffi().malloc
        except AttributeError:
            m = ctypes.CDLL(None).malloc
        m.argtypes = [ctypes.c_size_t]
        m.restype = ctypes.c_void_p
        _malloc = m
    return _malloc


def _malloc_cstr(text: str) -> int | None:
    data = text.encode("utf-8")
    p = _c_malloc()(len(data) + 1)
    if p:  # a NULL is passed on; the library reads it as "no rows"
        ctypes.memmove(p, data, len(data))
        ctypes.memset(p + len(data), 0, 1)
    return p


def version() -> str:
    """The version of the loaded engine."""
    return _ffi().leanelpi_version().decode()


# --- Terms -----------------------------------------------------------------------------------


@dataclass(frozen=True)
class Const:
    """An ELPI constant, e.g. `anna` or `tt`."""

    name: str

    def __repr__(self) -> str:
        return f"Const({self.name!r})"


@dataclass(frozen=True)
class App:
    """A constant applied to arguments: `pt 1 "x"` is `App("pt", (1, "x"))`."""

    name: str
    args: Tuple[Any, ...]

    def __init__(self, name: str, args: Iterable[Any] = ()) -> None:
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "args", tuple(args))

    def __repr__(self) -> str:
        return f"App({self.name!r}, {self.args!r})"


@dataclass(frozen=True)
class Var:
    """An unassigned variable: an output argument a host predicate receives, or an unbound
    answer. A host may not return one."""

    name: str


@dataclass(frozen=True)
class Opaque:
    """Any other term (a λ-term, an applied variable, an eigenvariable), as ELPI prints it.
    Only the engine produces these; a host may not return one."""

    printed: str


#: A decoded ELPI term: int, float, str, list (an ELPI list), Const, App, Var or Opaque.
Term = Union[int, float, str, list, Const, App, Var, Opaque]


def _decode(tree: Any) -> Any:
    """A JSON term tree from the engine as a Python value. Proper ELPI lists become Python
    lists; a list with an unbound tail stays `App("::", (head, tail))`."""
    if not isinstance(tree, dict):
        raise ElpiError(f"bad term tree: {tree!r}")
    if "c" in tree:
        name, args = tree["c"], tree.get("a")
        if args is None:
            return [] if name == "[]" else Const(name)
        args = [_decode(a) for a in args]
        if name == "::" and len(args) == 2 and isinstance(args[1], list):
            return [args[0], *args[1]]
        return App(name, args)
    if "i" in tree:
        return int(tree["i"])
    if "f" in tree:
        return float(tree["f"])
    if "s" in tree:
        return tree["s"]
    if "v" in tree:
        return Var(tree["v"])
    if "o" in tree:
        return Opaque(tree["o"])
    raise ElpiError(f"bad term tree: {tree!r}")


def _encode(value: Any) -> Any:
    """A Python value as a JSON term tree a host may return: bool (`tt`/`ff`), int, float,
    str, Const, App, and list or tuple (an ELPI list)."""
    if isinstance(value, bool):
        return {"c": "tt" if value else "ff"}
    if isinstance(value, int):
        return {"i": value}
    if isinstance(value, float):
        if not math.isfinite(value):
            raise TypeError(f"cannot pass {value} to ELPI")
        return {"f": value}
    if isinstance(value, str):
        return {"s": value}
    if isinstance(value, Const):
        return {"c": value.name}
    if isinstance(value, App):
        if not value.args:
            return {"c": value.name}
        return {"c": value.name, "a": [_encode(a) for a in value.args]}
    if isinstance(value, (list, tuple)):
        tree: Any = {"c": "[]"}
        for x in reversed(value):
            tree = {"c": "::", "a": [_encode(x), tree]}
        return tree
    raise TypeError(f"a host predicate cannot return {type(value).__name__} {value!r}")


# --- Answers ---------------------------------------------------------------------------------


@dataclass(frozen=True)
class Solution:
    """One answer: the query variables' values as printed by ELPI (`bindings`, also reached by
    `solution["X"]`), as Python values (`terms`), and the suspended constraints."""

    bindings: Dict[str, str]
    constraints: List[str] = field(default_factory=list)
    terms: Dict[str, Any] = field(default_factory=dict)

    def __getitem__(self, name: str) -> str:
        return self.bindings[name]


@dataclass(frozen=True)
class HostRun:
    """The outcome of `Program.solve_host_all`: the solutions, whether the search was
    exhausted (False when the limit cut it short) and the resolution steps it took."""

    solutions: List[Solution]
    exhausted: bool
    fuel_used: int


def _answer(lib: ctypes.CDLL, ptr: int) -> dict:
    try:
        doc = json.loads(ctypes.string_at(ptr).decode("utf-8"))
    finally:
        lib.leanelpi_free_string(ptr)
    doc["solutions"] = [
        Solution(s["bindings"], s["constraints"],
                 {k: _decode(t) for k, t in s.get("terms", {}).items()})
        for s in doc["solutions"]
    ]
    return doc


# --- Host predicates -------------------------------------------------------------------------

#: A host for `solve_host`: a mapping from predicate name to a function of the input
#: arguments, or one function of (name, all arguments).
Host = Union[Mapping[str, Callable[..., Any]], Callable[[str, List[Any]], Any]]


def _top_split(text: str, sep: str = ",") -> List[str]:
    """Split `text` at `sep` outside parentheses and brackets."""
    parts, depth, cur, i = [], 0, [], 0
    while i < len(text):
        ch = text[i]
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append("".join(cur))
            cur = []
            i += len(sep)
            continue
        cur.append(ch)
        i += 1
    parts.append("".join(cur))
    return [p.strip() for p in parts if p.strip()]


def _strip_comments(src: str) -> str:
    return re.sub(r"%[^\n]*", "", src)


#: Per argument of a host predicate: whether it is an input, and the head of its type
#: (`int`, `list`, `person`, ...; None for a type variable or a function type).
_Sig = Tuple[Tuple[bool, Optional[str]], ...]


def _type_head(arg: str) -> Optional[str]:
    t = arg[2:] if arg[:2] in ("i:", "o:") else arg
    t = t.strip()
    while t.startswith("(") and t.endswith(")"):
        t = t[1:-1].strip()
    if not t or "->" in t or not (t[0].islower()):
        return None
    return t.split()[0]


def _signature(name: str, sig: str) -> Optional[_Sig]:
    """Modes and type heads of `pred name ...` in signature text; None if not found.
    An argument without a mode is an output, as in the engine."""
    m = re.search(r"\bpred\s+" + re.escape(name) + r"(?=[\s.])(.*?)\.(?=\s|$)",
                  _strip_comments(sig), re.S)
    if m is None:
        return None
    return tuple((a.startswith("i:"), _type_head(a)) for a in _top_split(m.group(1)))


_IDENT = r"[a-z][\w.'?]*"


def _types_of(src: str) -> Tuple[frozenset, Dict[str, str]]:
    """The kinds declared in source text, and the head of each declared constant's result
    type (`type anna, marco person.` gives anna and marco the head `person`)."""
    src = _strip_comments(src)
    kinds = set()
    for m in re.finditer(r"\bkind\s+(.+?)\s+type\b", src):
        kinds.update(k.strip() for k in m.group(1).split(","))
    consts = {}
    for m in re.finditer(rf"\btype\s+({_IDENT}(?:\s*,\s*{_IDENT})*)\s+(.+?)\.(?=\s|$)", src, re.S):
        result = _top_split(m.group(2), "->")[-1] if m.group(2).strip() else ""
        head = _type_head(result)
        if head is not None:
            for c in m.group(1).split(","):
                consts[c.strip()] = head
    return frozenset(kinds), consts


def _check_output(pred: str, k: int, head: Optional[str], value: Any, kinds: frozenset,
                  consts: Mapping[str, str]) -> Any:
    """Catch a host value whose Python type cannot have the declared ELPI type (the engine does
    not type-check host answers); an int for a `float` argument becomes a float."""
    def bad() -> TypeError:
        return TypeError(f"output {k + 1} of {pred} has type {head}, "
                         f"got {type(value).__name__} {value!r}")
    literal = isinstance(value, (str, int, float))  # bool included
    if head == "int":
        if not isinstance(value, int) or isinstance(value, bool):
            raise bad()
    elif head == "string":
        if not isinstance(value, str):
            raise bad()
    elif head == "float":
        if not isinstance(value, (int, float)) or isinstance(value, bool):
            raise bad()
        return float(value)
    elif head == "bool":
        if literal and not isinstance(value, bool):
            raise bad()
    elif head == "list" or head in kinds:
        if literal:
            raise bad()
        if head in kinds and isinstance(value, (Const, App)):
            declared = consts.get(value.name)
            if declared is not None and declared != head:
                raise TypeError(f"output {k + 1} of {pred} has type {head}, "
                                f"got {value.name} of type {declared}")
    return value


def _rows(pred: str, result: Any, sig: Optional[_Sig], kinds: frozenset,
          consts: Mapping[str, str]) -> List[List[Any]]:
    """A host function's result as rows of encoded output terms. None or False is no rows,
    True is one row without outputs; otherwise an iterable of rows, each a tuple or list of
    output values or, for one output, the bare value."""
    if result is None or result is False:
        return []
    if result is True:
        return [[]]
    if isinstance(result, (str, bytes, int, float, Const, App)):
        raise TypeError(
            f"a host predicate returns an iterable of rows, not {type(result).__name__} "
            f"{result!r}; wrap a single answer as [({result!r},)]")
    heads = [h for inp, h in sig if not inp] if sig is not None else None
    out = []
    for row in result:
        items = list(row) if isinstance(row, (tuple, list)) else [row]
        if heads is not None and len(items) == len(heads):
            items = [_check_output(pred, k, h, x, kinds, consts)
                     for k, (h, x) in enumerate(zip(heads, items))]
        out.append([_encode(x) for x in items])
    return out


class _Trampoline:
    """The C callback for one `solve_host` run. Exceptions never cross into C: they become an
    `{"error": ...}` answer and are kept, to be chained to (or re-raised after) the run."""

    def __init__(self, host: Host, sigs: Mapping[str, Optional[_Sig]], kinds: frozenset,
                 consts: Mapping[str, str]) -> None:
        self.host = host
        self.sigs = sigs
        self.kinds = kinds
        self.consts = consts
        self.exc: BaseException | None = None
        self.c_fn = _HOST_FN(self._call)  # kept alive for the duration of the run

    def _dispatch(self, name: str, args: List[Any]) -> Any:
        host = self.host
        if isinstance(host, _MappingABC):
            fn = host.get(name)
            if fn is None:
                raise LookupError(f"no host function for '{name}'")
            sig = self.sigs.get(name)
            if sig is None or len(sig) != len(args):
                return fn(*args)
            return fn(*(a for a, (inp, _) in zip(args, sig) if inp))
        return host(name, args)

    def _fail(self, e: BaseException) -> int | None:
        if self.exc is None:
            self.exc = e
        try:
            return _malloc_cstr(json.dumps({"error": f"{type(e).__name__}: {e}"}))
        except BaseException:
            return None

    def _call(self, _ctx: Any, c_name: bytes, c_args: bytes) -> int | None:
        # Nothing may unwind into C: ctypes would print the exception and return NULL, which
        # the engine reads as "no rows", silently turning an error into a failure.
        try:
            name = c_name.decode("utf-8")
            args = [_decode(t) for t in json.loads(c_args.decode("utf-8"))]
            result = self._dispatch(name, args)
            doc = {"rows": _rows(name, result, self.sigs.get(name), self.kinds, self.consts)}
            return _malloc_cstr(json.dumps(doc, ensure_ascii=False, allow_nan=False))
        except BaseException as e:  # noqa: B902
            return self._fail(e)


# --- Programs --------------------------------------------------------------------------------


# @tg: implements:: [[openspec:language-bindings#Python binding]]
class Program:
    """A compiled ELPI program. Programs are immutable: `assert_clause` and `declare` return a
    new one."""

    def __init__(self, source: str = "", *, _handle: int | None = None,
                 _sigs: Mapping[str, Optional[_Sig]] | None = None,
                 _kinds: frozenset = frozenset(),
                 _consts: Mapping[str, str] | None = None) -> None:
        lib = _ffi()
        if _handle is None:
            err = ctypes.c_char_p()
            _handle = lib.leanelpi_load(source.encode(), ctypes.byref(err))
            if _handle == _INVALID:
                raise ElpiError(_take(lib, err) or "load failed")
        self._handle: int | None = _handle
        # The host predicates declared on this program (modes and type heads of their
        # arguments), and the kinds and constants its source declares: they route host
        # calls and catch host answers of the wrong type, which the engine does not check.
        self._sigs: Dict[str, Optional[_Sig]] = dict(_sigs or {})
        kinds, consts = _types_of(source)
        self._kinds = _kinds | kinds
        self._consts: Dict[str, str] = {**(_consts or {}), **consts}

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
        return Program(clause, _handle=h, _sigs=self._sigs, _kinds=self._kinds,
                       _consts=self._consts)

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
        doc = _answer(lib, ptr)
        return doc["solutions"], doc["exhausted"]

    def first(self, query: str, *, fuel: int | None = None) -> dict[str, str] | None:
        """The bindings of the first solution, or None when the query fails."""
        sols = self.solve(query, limit=1, fuel=fuel)
        return sols[0].bindings if sols else None

    def ask(self, query: str, *, fuel: int | None = None) -> bool:
        """Whether the query has a solution."""
        return self.first(query, fuel=fuel) is not None

    # -- host predicates --

    def declare(self, signature: str, name: str | None = None) -> "Program":
        """A new program in which a predicate is answered by Python during `solve_host`.

        `signature` declares it, e.g. `"pred same_person i:string, o:person."`, possibly
        with the kinds and types it uses; `name` defaults to the name after its first
        `pred`. The program may already declare the predicate, so its clauses can call it,
        but must not have clauses for it. This program is unchanged. A query that reaches
        the predicate through `solve` (with no host) raises ElpiError."""
        if name is None:
            m = re.search(r"\bpred\s+([^\s.,]+)", _strip_comments(signature))
            if m is None:
                raise ValueError(f"no 'pred' declaration in {signature!r}; pass name=")
            name = m.group(1)
        lib = _ffi()
        if not hasattr(lib, "leanelpi_declare"):
            raise ElpiError(f"libleanelpi {version()} has no host predicates (needs 0.4.0)")
        err = ctypes.c_char_p()
        h = lib.leanelpi_declare(self._live(), name.encode(), signature.encode(),
                                 ctypes.byref(err))
        if h == _INVALID:
            raise ElpiError(_take(lib, err) or "declare failed")
        return Program(signature, _handle=h, _sigs={**self._sigs, name: _signature(name, signature)},
                       _kinds=self._kinds, _consts=self._consts)

    def solve_host_all(self, query: str, host: Host, *, limit: int | None = None,
                       fuel: int | None = None) -> HostRun:
        """Run `query`, answering every declared host predicate with `host`, synchronously
        on this thread.

        `host` is either a mapping from predicate name to a function that takes the
        predicate's input-mode (`i:`) arguments, positionally, or one function
        `host(name, args)` that takes the name and every argument (unbound ones as `Var`).
        Either returns the answers as an iterable of rows, one tuple of output-mode (`o:`)
        values per answer, in argument order (a bare value is a one-output row); an empty
        iterable or None means the call fails, True means it succeeds once (no outputs).
        Values are int, float, str, bool (`tt`/`ff`), Const, App and list. The engine does
        not type-check host answers; this binding rejects a value that cannot have the
        declared output type (a str for `o:person`, a constant declared as a city for
        `o:person`) and turns an int for `o:float` into a float. A constant the program does
        not know is an error in the engine.

        An exception in `host` stops the run and raises ElpiError with the exception as its
        `__cause__` (KeyboardInterrupt and SystemExit are re-raised as they are)."""
        lib = _ffi()
        if not hasattr(lib, "leanelpi_solve_host"):
            raise ElpiError(f"libleanelpi {version()} has no host predicates (needs 0.4.0)")
        tramp = _Trampoline(host, self._sigs, self._kinds, self._consts)
        err = ctypes.c_char_p()
        ptr = lib.leanelpi_solve_host(self._live(), query.encode(), limit or 0, fuel or 0,
                                      tramp.c_fn, None, ctypes.byref(err))
        exc = tramp.exc
        if not ptr:
            msg = _take(lib, err) or "query failed"
            if exc is not None and not isinstance(exc, Exception):
                raise exc
            raise ElpiError(msg) from exc
        doc = _answer(lib, ptr)
        if exc is not None and not isinstance(exc, Exception):
            raise exc
        return HostRun(doc["solutions"], doc["exhausted"], doc.get("fuelUsed", 0))

    def solve_host(self, query: str, host: Host, *, limit: int | None = None,
                   fuel: int | None = None) -> list[Solution]:
        """The solutions of `solve_host_all`."""
        return self.solve_host_all(query, host, limit=limit, fuel=fuel).solutions

    def first_host(self, query: str, host: Host, *, fuel: int | None = None) -> Solution | None:
        """The first solution of `solve_host` (with its `terms`), or None when it fails."""
        sols = self.solve_host(query, host, limit=1, fuel=fuel)
        return sols[0] if sols else None

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
