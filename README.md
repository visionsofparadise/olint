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

Rust unit tests belong beside their implementation in `*.test.rs` files, included by a private `#[cfg(test)]` module with `#[path = "filename.test.rs"]`. Empty suites pass until behavior needs tests.
