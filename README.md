# Lean verification example

[`lean/Verification.lean`](lean/Verification.lean) contains two Lean 4 proofs:

- `square_of_sum`: for all real numbers `a` and `b`,
  `(a + b)² = a² + 2ab + b²`.
- `missing_middle_term_counterexample`: omitting `2ab` fails at `a = b = 1`.

`ring` constructs the algebraic proof. `norm_num` proves the numerical
counterexample. Lean's kernel checks the proofs; there are no `sorry`
placeholders.

## Run

Install [elan, Lean's toolchain manager](https://github.com/leanprover/elan#installation),
and ensure `lean` and `lake` are on your `PATH`. Then:

```sh
cd lean
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
lake build
```

The project pins Lean and Mathlib to matching `v4.24.0` releases. The first run
downloads the toolchain, dependencies, and precompiled Mathlib modules.
A successful build verifies both theorems.

## Try an incorrect claim

In `square_of_sum`, remove `2 * a * b +` from the right-hand side and run
`lake build` again. The proof fails because `ring` cannot establish the false
identity. Restore the term to make the build pass.

For more examples, see
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html).
