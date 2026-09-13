# olint

Asymptotic cost lint for TypeScript.

olint reports the asymptotic cost of every function in a TypeScript project, composed from loops, standard library calls, user calls, and recursion, and fails a project whose public functions exceed their limit.

## Usage

```sh
olint [tsconfig] [--report] [--min N] [--config path] [--types auto|oracle|syntactic] [--strings-constant] [--no-callbacks]
```

- `tsconfig` is the project's tsconfig path, `tsconfig.json` by default.
- `--report` prints the full per-function report in place of lint findings.
- `--min N` sets the smallest cost exponent a report row shows, `2` (`O(N^2)`) by default; both `--min N` and `--min=N` work.
- `--config path` sets the config file path, `olint.config.json` next to the tsconfig by default.
- `--types` picks the type source: `auto` (default) uses the oracle when `node` and the project's own `typescript` resolve, and falls back to declarations alone with one stderr line when they do not; `oracle` requires the oracle and exits with an error when it is unavailable; `syntactic` reads declarations alone and never spawns `node`.
- `--strings-constant` costs string methods as constant instead of linear.
- `--no-callbacks` costs a callback parameter as unknown instead of substituting its argument.

Exit codes:

| code | meaning                                                                                              |
| ---- | ---------------------------------------------------------------------------------------------------- |
| `0`  | every public function is within its limit, or `--report` ran                                         |
| `1`  | a public function exceeds its limit                                                                  |
| `2`  | a usage, configuration, project, or required-oracle error, printed on stderr with an `olint:` prefix |

## Configuration

`olint.config.json` next to the tsconfig, or `--config path`:

```json
{
	"max": "O(N^2)",
	"entrypoints": { "src/index.ts": "O(N^2)", "src/react/index.ts": "O(N^3)" },
	"ignore": ["src/generated/**", "**/*.fixture.ts"]
}
```

| key           | meaning                                                                  | default                                                                                                                                                             |
| ------------- | ------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `max`         | the limit an entrypoint gets when it has none of its own                 | `O(N^2)`                                                                                                                                                            |
| `entrypoints` | entry files and the limit each one grants its exports                    | the package's `exports`, or its `source`, `types`, `module`, and `main` fields, resolved from a built path to source: `dist/x.js` to `src/x.ts` or `src/x/index.ts` |
| `ignore`      | globs, relative to the tsconfig folder, whose functions are never public | none                                                                                                                                                                |

A public function is one reachable from an entrypoint's exports, following re-exports, including the non-private methods of exported classes. Its cost already includes everything it calls, so internal helpers are covered through the public functions that reach them and appear in their chains. A function exported from two entrypoints takes the stricter limit, and `@perf max O(N^3)` on a function replaces the limit it inherited from its entrypoint.

## Annotations

A comment directly above the statement or declaration it governs, as a line comment or JSDoc:

```ts
// @perf cold
/** @perf O(N) */
```

A tag governs the next statement. Inside a body it applies to the statement that follows it, and a tag on a `const f = () => {}` statement or a class property governs the function it holds.

| directive | placed on         | effect                                                                                                                          |
| --------- | ----------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| `ignore`  | function          | callers see `O(1)` and the report omits it                                                                                      |
| `ignore`  | statement         | the subtree costs `O(1)`                                                                                                        |
| `cold`    | function          | callers see `O(1)`; the report still carries the function on its own line, marked `[@perf cold]`, with its real cost            |
| `cold`    | statement         | the statement costs `O(1)`                                                                                                      |
| `hot`     | statement         | within the enclosing block, only hot statements count, and the other branches of an enclosing `if`, `switch`, or `try` drop out |
| `bounded` | loop              | the loop's factor becomes `1`; the body still counts                                                                            |
| `bounded` | other statement   | the statement costs `O(1)`                                                                                                      |
| `O(...)`  | statement or loop | the stated cost replaces the statement's total                                                                                  |
| `O(...)`  | function          | callers see the stated cost; the report still carries the function with its real cost, marked `[@perf O(...)]`                  |

`O(...)` accepts `O(1)`, `O(log N)`, `O(N)`, `O(N log N)`, `O(N^k)`, and `O(N^k log N)`.

## Types

Declared types answer most cost questions from the source's own syntax. The project's own TypeScript, run through `node`, answers the rest under `--types=auto` or `--types=oracle`. `npm run integration` needs both `node` and the project's `typescript` on the path.

Use Node 24 LTS, npm 12, and Rust through rustup. The committed toolchain selects rustfmt and Clippy.

```sh
npm install
npm run check
npm run unit
npm run build
npm start
```

`npm run fix` applies available formatting and lint fixes. Installation activates commitlint and Trivy git hooks and installs pinned Rust lint tools.

Rust unit tests belong beside their implementation in `*.test.rs` files, included by a private `#[cfg(test)]` module with `#[path = "filename.test.rs"]`. Empty suites pass until behavior needs tests.
