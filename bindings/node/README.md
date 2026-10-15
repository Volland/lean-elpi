# @lean-elpi/leanelpi (Node.js)

Run ELPI (λProlog) programs on the [LeanElpi](https://volland.github.io/lean-elpi/) engine from
Node.js. The native library comes with the package for macOS and Linux (x64 and arm64); no
compiler is needed.

```js
const { Program } = require('@lean-elpi/leanelpi');

const p = new Program('pred n o:int.\nn 1.\nn 2.');
p.solve('n X').map((s) => s.bindings.X);   // ['1', '2']
p.first('n X');                            // { X: '1' }
p.assertClause('n 3.').solve('n X').length // 3, and p is unchanged
```

Calls are synchronous. Failure gives `null` or an empty array; engine errors throw `ElpiError`.
TypeScript declarations are included. Guide: <https://volland.github.io/lean-elpi/book/bindings/>.
