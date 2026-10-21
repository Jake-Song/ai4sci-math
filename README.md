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
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Data.Real.Sqrt Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
lake build
```

The project pins Lean and Mathlib to matching `v4.24.0` releases. The first run
downloads the toolchain, dependencies, and precompiled Mathlib modules.
A successful build verifies all theorems in the four Lean files. The Collatz
files prove partial and conditional results, not the full conjecture.

## 피타고라스 정리

[`lean/Pythagoras.lean`](lean/Pythagoras.lean)은 평면의 세 점 `A`, `B`, `C`에 대해
벡터 `AB`와 `AC`의 내적이 0이면 `AB² + AC² = BC²`임을 증명합니다.
거리는 좌표 차의 제곱합의 제곱근으로 정의하며, 좌표 전개의 교차항이
직각 조건으로 사라지는 것을 이용합니다. `sorry` 없이 Lean이 검증합니다.

```sh
cd lean
lake build Pythagoras
```

## 콜라츠 추측 연구

[한국어 연구 기록](collatz/README.md)에서 가설, 단계별 증명, 반례와 남은
증명 의무를 확인할 수 있습니다. [Lean 코드](lean/Collatz.lean)는 전체 추측과
하강 명제의 동치, 세 가지 경우의 하강, 두 후보의 반례를 검증합니다.
**전체 콜라츠 추측을 증명한 것은 아닙니다.**

```sh
cd lean
lake build Collatz
lake env lean Collatz.lean
```

두 번째 명령은 주요 정리의 공리 의존성도 출력합니다. 미해결 가설을 참으로
선언하지 않으며, 조건부 정리는 가정을 인자로 명시합니다.

[추가 분석](lean/CollatzAnalysis.lean)은 공통 하강 횟수 상한이 존재하지 않음을
증명하고, 누적 덧셈 항을 포함한 정확한 하강 조건을 검증합니다.
한국어 연구 기록의 5–7절에서 기존 전략의 한계와 새 증명을 설명합니다.

```sh
cd lean
lake build CollatzAnalysis
lake env lean CollatzAnalysis.lean
```

## Try an incorrect claim

In `square_of_sum`, remove `2 * a * b +` from the right-hand side and run
`lake build` again. The proof fails because `ring` cannot establish the false
identity. Restore the term to make the build pass.

For more examples, see
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html).
