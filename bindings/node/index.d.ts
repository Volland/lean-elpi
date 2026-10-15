/** One answer: the query variables' values, as printed by ELPI, and suspended constraints. */
export interface Solution {
  bindings: Record<string, string>;
  constraints: string[];
}

export interface SolveOptions {
  /** Stop after this many solutions (default: all). */
  limit?: number;
  /** Resolution-step budget (default: the engine's default). */
  fuel?: number;
}

/** A parse, type or runtime error reported by the engine. */
export class ElpiError extends Error {
  name: 'ElpiError';
}

/** A compiled ELPI program. Programs are immutable: `assertClause` returns a new one. */
export class Program {
  /** Compile `source`. Throws `ElpiError` on a parse or type error. */
  constructor(source?: string);
  /** A new program with `clause` added; this program is unchanged. */
  assertClause(clause: string): Program;
  /** `exhausted` is false when `limit` cut the search short. */
  solveAll(query: string, options?: SolveOptions): { solutions: Solution[]; exhausted: boolean };
  solve(query: string, options?: SolveOptions): Solution[];
  /** The bindings of the first solution, or `null` when the query fails. */
  first(query: string, options?: { fuel?: number }): Record<string, string> | null;
  ask(query: string, options?: { fuel?: number }): boolean;
  /** Free the program. Further use throws. */
  close(): void;
  [Symbol.dispose](): void;
}

/** The version of the loaded engine. */
export function version(): string;
