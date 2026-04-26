# Codex Report

## Summary

`moon check --deny-warn` passes after the warning cleanup work.

The final quality gate `moon test --target all` did not complete. It stayed in
the `chapter19` blackbox test runner for more than 7 minutes while the runner
used 100% CPU, so it was interrupted and narrowed down.

## Commands Run

- `moon check --deny-warn`
  - Result: passed.
- `moon test --target all`
  - Result: interrupted after more than 7 minutes.
  - Observed process: `chapter19.blackbox_test.wasm` consuming 100% CPU.
- `timeout 60s moon test chapter19 --target wasm -v`
  - Result: timed out.
- `timeout 45s moon test chapter19/chapter19_test.mbt --target wasm -v`
  - Result: passed, 46 tests.
- `timeout 45s moon test chapter19/scheduler_test.mbt --target wasm -v`
  - Result: failed.
  - Failing tests:
    - `scheduler: store in if`: expected object.
    - `scheduler: store in if 2`: expected `2`, got `0`.
- `timeout 45s moon test chapter19/chapter13_test.mbt --target wasm -v`
  - Result: timed out.

## Human Follow-Up Needed

The remaining issue is runtime test behavior in `chapter19`, not a dependency
error and not a MoonBit warning. Fixing it safely requires domain-specific
debugging of the chapter19 evaluator/parser/scheduler behavior.

The repository is otherwise warning-clean under:

```bash
moon check --deny-warn
```
