'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const { Program, ElpiError, version } = require('..');

const APP = 'pred app i:list int, i:list int, o:list int.\n' +
  'app [] L L.\napp [X|Xs] L [X|R] :- app Xs L R.';
const N3 = 'pred n o:int.\nn 1.\nn 2.\nn 3.';

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Load and query]]
test('load and query', () => {
  const p = new Program(N3);
  assert.deepEqual(p.solve('n X').map((s) => s.bindings.X), ['1', '2', '3']);
  assert.equal(p.solveAll('n X').exhausted, true);
  assert.match(version(), /^\d+\.\d+\.\d+$/);
});

// @tg: verifies:: [[openspec:language-bindings#Node.js binding#Query from Node]]
test('first solution', () => {
  assert.deepEqual(new Program(APP).first('app [1,2] [3] R'), { R: '[1, 2, 3]' });
});

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Limit stops the search]]
test('limit stops the search', () => {
  const r = new Program(N3).solveAll('n X', { limit: 2 });
  assert.equal(r.solutions.length, 2);
  assert.equal(r.exhausted, false);
});

// @tg: verifies:: [[openspec:language-bindings#Node.js binding#Node failure and errors]]
test('failure is null, errors throw', () => {
  const p = new Program('pred q o:int.\nq 1.');
  assert.equal(p.first('q 2'), null);
  assert.equal(p.ask('q 2'), false);
  assert.throws(() => new Program('pred q o:int.\nq foo bar.'), ElpiError);
  assert.throws(() => new Program(APP).solve('nope X'), ElpiError);
});

// @tg: verifies:: [[openspec:language-bindings#Node.js binding#Persistent assert from Node]]
test('assert is persistent', () => {
  const p = new Program('pred q o:int.\nq 1.');
  const p2 = p.assertClause('q 2.');
  assert.deepEqual(p.solve('q X').map((s) => s.bindings.X), ['1']);
  assert.deepEqual(p2.solve('q X').map((s) => s.bindings.X), ['1', '2']);
});

// @tg: verifies:: [[openspec:language-bindings#Handle-based C ABI#Errors are reported, not raised through C]]
test('closed program throws', () => {
  const p = new Program(APP);
  p.close();
  p.close();
  assert.throws(() => p.first('app [] [] R'), /closed/);
});
