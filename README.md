# olint

Asymptotic cost lint for TypeScript.

Use Node 24 LTS, npm 12, and Rust through rustup. The committed toolchain selects rustfmt and Clippy.

```sh
npm install
npm run check
npm run unit
npm run build
npm start
```

`npm run fix` applies available formatting and lint fixes. Installation activates commitlint and Trivy git hooks and installs pinned Rust lint tools.

Dev builds omit debug info. Every npm script that builds Rust first runs `node sweep.mjs`, which removes `target/` artifacts older than 14 days with `cargo sweep --time 14` and skips with a notice when cargo-sweep is missing (`cargo binstall cargo-sweep`).

Rust unit tests belong beside their implementation in `*.test.rs` files, included by a private `#[cfg(test)]` module with `#[path = "filename.test.rs"]`. Empty suites pass until behavior needs tests.
