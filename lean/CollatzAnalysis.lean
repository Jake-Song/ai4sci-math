import Collatz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Collatz: limits of bounded descent and an exact descent criterion

전체 추측의 증명이 아니다. 기존 가설 H를 사용하지 않고, 고정 횟수 접근의
한계와 실제 궤도의 불변식을 검증한다. 설명: ../collatz/README.md.
-/

namespace Collatz

/-- L4: 기존 재귀 정의를 마지막 한 단계 기준으로도 전개할 수 있다. -/
theorem iterate_succ_last (k n : ℕ) : iterate (k + 1) n = step (iterate k n) := by
  simpa only [iterate] using iterate_add k 1 n

/-- M1: 양수 t에 대한 홀수 단계와 뒤따르는 짝수 단계의 합성. -/
theorem odd_even_pair {t : ℕ} (ht : 0 < t) :
    iterate 2 (2 * t - 1) = 3 * t - 1 := by
  have hodd : step (2 * t - 1) = 6 * t - 2 := by
    rw [step_odd (by omega)]
    omega
  have heven : step (6 * t - 2) = 3 * t - 1 := by
    rw [step_even (by omega)]
    omega
  simp only [iterate, hodd, heven]

/-- M2: 2의 인수가 j개 있으면 j쌍의 홀수·짝수 단계를 정확히 전개할 수 있다. -/
theorem odd_even_block (j r a : ℕ) (ha : 0 < a) :
    iterate (2 * j) (a * 2 ^ (j + r) - 1) = 3 ^ j * a * 2 ^ r - 1 := by
  induction j generalizing a with
  | zero => simp [iterate]
  | succ j ih =>
    have hpow : a * 2 ^ (j + 1 + r) = 2 * (a * 2 ^ (j + r)) := by
      rw [show j + 1 + r = (j + r) + 1 by omega, Nat.pow_succ]
      ring
    have ht : 0 < a * 2 ^ (j + r) :=
      Nat.mul_pos ha (Nat.pow_pos (by decide))
    rw [show 2 * (j + 1) = 2 + 2 * j by omega, iterate_add, hpow,
      odd_even_pair ht]
    rw [show 3 * (a * 2 ^ (j + r)) = (3 * a) * 2 ^ (j + r) by ring]
    rw [ih (3 * a) (by omega), Nat.pow_succ]
    congr 1
    ring

/-- M3: 2^m-1의 짝수 시각 값. j=m도 포함한다. -/
theorem mersenne_even_iterate (m j : ℕ) (hj : j ≤ m) :
    iterate (2 * j) (2 ^ m - 1) = 3 ^ j * 2 ^ (m - j) - 1 := by
  have h := odd_even_block j (m - j) 1 (by decide)
  simpa only [Nat.add_sub_of_le hj, one_mul, mul_one] using h

/-- M4: 2^m-1의 홀수 시각 값. j<m이 필요하다. -/
theorem mersenne_odd_iterate (m j : ℕ) (hj : j < m) :
    iterate (2 * j + 1) (2 ^ m - 1) = 3 ^ (j + 1) * 2 ^ (m - j) - 2 := by
  rw [iterate_succ_last, mersenne_even_iterate m j (by omega)]
  have hpow : 2 ^ (m - j) = 2 ^ (m - j - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hpos : 0 < 3 ^ j * 2 ^ (m - j - 1) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have heven : 3 ^ j * 2 ^ (m - j) = 2 * (3 ^ j * 2 ^ (m - j - 1)) := by
    rw [hpow]
    ring
  rw [step_odd (by rw [heven]; omega), Nat.pow_succ]
  have hlarge : 1 ≤ 3 ^ j * 2 ^ (m - j) := by rw [heven]; omega
  have hmul : 3 ^ j * 3 * 2 ^ (m - j) = 3 * (3 ^ j * 2 ^ (m - j)) := by ring
  rw [hmul]
  omega

/-- M5: 처음 2m회 동안 시작값보다 작아지지 않는다. m=0에서도 성립한다. -/
theorem mersenne_no_descent (m k : ℕ) (hk : k ≤ 2 * m) :
    2 ^ m - 1 ≤ iterate k (2 ^ m - 1) := by
  have hpower (j : ℕ) (hj : j ≤ m) : 2 ^ m ≤ 3 ^ j * 2 ^ (m - j) := by
    calc
      2 ^ m = 2 ^ j * 2 ^ (m - j) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hj]
      _ ≤ 3 ^ j * 2 ^ (m - j) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j)
  by_cases he : k % 2 = 0
  · have heq : k = 2 * (k / 2) := by omega
    rw [heq, mersenne_even_iterate m (k / 2) (by omega)]
    exact Nat.sub_le_sub_right (hpower (k / 2) (by omega)) 1
  · have heq : k = 2 * (k / 2) + 1 := by omega
    have hj : k / 2 < m := by omega
    rw [heq, mersenne_odd_iterate m (k / 2) hj, Nat.pow_succ]
    have hp := hpower (k / 2) (by omega)
    have hpos : 0 < 3 ^ (k / 2) * 2 ^ (m - k / 2) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    have hmul : 3 ^ (k / 2) * 3 * 2 ^ (m - k / 2) =
        3 * (3 ^ (k / 2) * 2 ^ (m - k / 2)) := by ring
    rw [hmul]
    omega

/-- U1: 어떤 B를 정해도 처음 B회 동안 하강하지 않는 시작값이 있다. -/
theorem arbitrarily_long_non_descent (B : ℕ) :
    ∃ n, 1 < n ∧ ∀ k, k ≤ B → n ≤ iterate k n := by
  -- B=0에서도 n>1을 보장하기 위해 지수에 2를 더한다.
  refine ⟨2 ^ (B + 2) - 1, ?_, ?_⟩
  · have hp : 0 < 2 ^ B := Nat.pow_pos (by decide)
    rw [Nat.pow_add]
    norm_num
    omega
  · intro k hk
    exact mersenne_no_descent (B + 2) k (by omega)

/-- U2: 모든 시작값에 공통인 유한 하강 횟수 상한은 존재하지 않는다. -/
theorem no_uniform_descent_bound :
    ¬ (∃ B, ∀ n, 1 < n → ∃ k, 0 < k ∧ k ≤ B ∧ iterate k n < n) := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn, hstay⟩ := arbitrarily_long_non_descent B
  obtain ⟨k, _hk, hle, hlt⟩ := hB n hn
  have hge := hstay k hle
  omega

/-- 실제 궤도의 홀수/짝수 단계 수와, 공통 분모를 적용한 누적 덧셈 항. -/
structure OrbitStats where
  oddSteps : ℕ
  evenSteps : ℕ
  offset : ℕ
  deriving DecidableEq, Repr

/-- A1: 실제 반복값의 짝홀로만 갱신한다. 임의의 짝홀 패턴을 가정하지 않는다. -/
def orbitStats : ℕ → ℕ → OrbitStats
  | 0, _ => ⟨0, 0, 0⟩
  | k + 1, n =>
    let s := orbitStats k n
    if iterate k n % 2 = 0 then
      { s with evenSteps := s.evenSteps + 1 }
    else
      { s with oddSteps := s.oddSteps + 1, offset := 3 * s.offset + 2 ^ s.evenSteps }

/-- A2: 홀수 단계와 짝수 단계의 합은 전체 반복 횟수다. -/
theorem orbitStats_count (k n : ℕ) :
    (orbitStats k n).oddSteps + (orbitStats k n).evenSteps = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold orbitStats
    split <;> dsimp <;> omega

/-- A3: 2^e C^k(n) = 3^o n + b. 0을 포함한 모든 자연수에서 성립한다. -/
theorem orbit_affine_identity (k n : ℕ) :
    2 ^ (orbitStats k n).evenSteps * iterate k n =
      3 ^ (orbitStats k n).oddSteps * n + (orbitStats k n).offset := by
  induction k with
  | zero => simp [orbitStats, iterate]
  | succ k ih =>
    by_cases he : iterate k n % 2 = 0
    · have hdiv : iterate k n / 2 * 2 = iterate k n :=
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he)
      simp only [orbitStats, he, ↓reduceIte, iterate_succ_last, step_even he,
        Nat.pow_succ]
      calc
        _ = 2 ^ (orbitStats k n).evenSteps * (iterate k n / 2 * 2) := by ring
        _ = _ := by rw [hdiv]; exact ih
    · simp only [orbitStats, ↓reduceIte, iterate_succ_last, step, he,
        Nat.pow_succ]
      calc
        _ = 3 * (2 ^ (orbitStats k n).evenSteps * iterate k n) +
            2 ^ (orbitStats k n).evenSteps := by ring
        _ = _ := by rw [ih]; ring

/-- A4: 배율뿐 아니라 누적 덧셈 항을 포함해야 정확한 하강 판정이 된다. -/
theorem descent_iff_affine_lt (k n : ℕ) :
    iterate k n < n ↔
      3 ^ (orbitStats k n).oddSteps * n + (orbitStats k n).offset <
        2 ^ (orbitStats k n).evenSteps * n := by
  rw [← orbit_affine_identity]
  exact (Nat.mul_lt_mul_left (Nat.pow_pos (by decide))).symm

/-- F3: 배율 27/32<1이어도 누적항 47 때문에 3에서 8회 후의 값은 4다. -/
theorem slope_only_counterexample :
    orbitStats 8 3 = ⟨3, 5, 47⟩ ∧
    3 ^ (orbitStats 8 3).oddSteps < 2 ^ (orbitStats 8 3).evenSteps ∧
    iterate 8 3 = 4 ∧ ¬ (iterate 8 3 < 3) := by
  decide

-- E2: 경계값과 기존 하강 정리의 계수를 커널로 검사한다.
example : iterate 0 (2 ^ 1 - 1) = 1 := rfl
example : iterate 2 (2 ^ 1 - 1) = 2 := rfl
example : orbitStats 0 0 = ⟨0, 0, 0⟩ := rfl
example : orbitStats 3 5 = ⟨1, 2, 1⟩ := rfl
example : orbitStats 6 3 = ⟨2, 4, 5⟩ := rfl
example : ∃ n, 1 < n ∧ ∀ k, k ≤ 0 → n ≤ iterate k n :=
  arbitrarily_long_non_descent 0

#print axioms mersenne_even_iterate
#print axioms mersenne_odd_iterate
#print axioms mersenne_no_descent
#print axioms no_uniform_descent_bound
#print axioms orbitStats_count
#print axioms orbit_affine_identity
#print axioms descent_iff_affine_lt
#print axioms slope_only_counterexample

end Collatz
