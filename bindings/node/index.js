'use strict';
// Node.js bindings for LeanElpi. Loads libleanelpi through koffi (no compiler needed).

const fs = require('fs');
const path = require('path');

const INVALID = 0xffffffffffffffffn;

class ElpiError extends Error {
  constructor(message) {
    super(message);
    this.name = 'ElpiError';
  }
}

function libraryName() {
  const ext = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
  return `libleanelpi.${ext}`;
}

function* candidates() {
  const name = libraryName();
  if (process.env.LEANELPI_LIB) yield process.env.LEANELPI_LIB;
  // The per-platform package, installed through optionalDependencies.
  try {
    yield path.join(path.dirname(require.resolve(`@lean-elpi/leanelpi-${process.platform}-${process.arch}/package.json`)), name);
  } catch (_) { /* not installed */ }
  // A source checkout: bindings/node/../../dist.
  yield path.join(__dirname, '..', '..', 'dist', name);
}

let ffi = null;

function load() {
  if (ffi) return ffi;
  const tried = [];
  let file = null;
  for (const c of candidates()) {
    tried.push(c);
    if (fs.existsSync(c)) { file = c; break; }
  }
  if (!file) {
    throw new Error(
      `libleanelpi not found for ${process.platform}-${process.arch}. Install the platform package ` +
      `(@lean-elpi/leanelpi-${process.platform}-${process.arch}), build it with scripts/build-ffi.sh, or set ` +
      `LEANELPI_LIB. Tried:\n  ${tried.join('\n  ')}`);
  }
  const koffi = require('koffi');
  const lib = koffi.load(file);
  const f = {
    koffi,
    init: lib.func('int leanelpi_init(_Out_ void **err)'),
    version: lib.func('const char *leanelpi_version()'),
    load: lib.func('uint64_t leanelpi_load(const char *src, _Out_ void **err)'),
    assert: lib.func('uint64_t leanelpi_assert(uint64_t p, const char *clause, _Out_ void **err)'),
    free: lib.func('void leanelpi_free(uint64_t p)'),
    solve: lib.func('void *leanelpi_solve(uint64_t p, const char *q, uint64_t limit, uint64_t fuel, _Out_ void **err)'),
    freeString: lib.func('void leanelpi_free_string(void *s)'),
  };
  const err = [null];
  if (f.init(err) !== 0) throw new ElpiError(takeString(f, err) || 'cannot start the Lean runtime');
  ffi = f;
  return f;
}

/** Read and release a string the library allocated. */
function takeString(f, ptr) {
  const p = Array.isArray(ptr) ? ptr[0] : ptr;
  if (!p) return null;
  const s = f.koffi.decode(p, 'char', -1);
  f.freeString(p);
  return s;
}

const registry = typeof FinalizationRegistry === 'function'
  ? new FinalizationRegistry((h) => { try { ffi && ffi.free(h); } catch (_) { /* shutting down */ } })
  : null;

// @tg: implements:: [[openspec:language-bindings#Node.js binding]]
class Program {
  /** Compile `source`. Throws `ElpiError` on a parse or type error. */
  constructor(source = '', handle) {
    const f = load();
    if (handle === undefined) {
      const err = [null];
      handle = BigInt(f.load(String(source), err));
      if (handle === INVALID) throw new ElpiError(takeString(f, err) || 'load failed');
    }
    this._handle = handle;
    if (registry) registry.register(this, handle, this);
  }

  _live() {
    if (this._handle === null) throw new Error('program is closed');
    return this._handle;
  }

  /** A new program with `clause` added; this program is unchanged. */
  assertClause(clause) {
    const f = load();
    const err = [null];
    const h = BigInt(f.assert(this._live(), String(clause), err));
    if (h === INVALID) throw new ElpiError(takeString(f, err) || 'assert failed');
    return new Program('', h);
  }

  /** `{ solutions, exhausted }`; `exhausted` is false when `limit` cut the search short. */
  solveAll(query, { limit = 0, fuel = 0 } = {}) {
    const f = load();
    const err = [null];
    const ptr = f.solve(this._live(), String(query), BigInt(limit), BigInt(fuel), err);
    if (!ptr) throw new ElpiError(takeString(f, err) || 'query failed');
    const doc = JSON.parse(takeString(f, ptr));
    return { solutions: doc.solutions, exhausted: doc.exhausted };
  }

  /** Up to `limit` solutions (all when omitted): `[{ bindings, constraints }]`. */
  solve(query, options) {
    return this.solveAll(query, options).solutions;
  }

  /** The bindings of the first solution, or `null` when the query fails. */
  first(query, { fuel = 0 } = {}) {
    const s = this.solve(query, { limit: 1, fuel });
    return s.length ? s[0].bindings : null;
  }

  /** Whether the query has a solution. */
  ask(query, options) {
    return this.first(query, options) !== null;
  }

  /** Free the program. Further use throws. */
  close() {
    if (this._handle !== null) {
      if (registry) registry.unregister(this);
      load().free(this._handle);
      this._handle = null;
    }
  }

  [Symbol.dispose]() { this.close(); }
}

/** The version of the loaded engine. */
function version() {
  return load().version();
}

module.exports = { Program, ElpiError, version };
