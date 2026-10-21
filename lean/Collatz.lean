import Mathlib.Data.Nat.Basic

/-!
# Collatz research: verified lemmas, not a proof of the conjecture

명제 ID와 한국어 증명은 ../collatz/README.md를 참고하세요.
미해결 가설은 Prop으로 정의할 뿐, 참으로 선언하지 않습니다.
-/

namespace Collatz

/-- 표준 콜라츠 함수. 0에서도 정의되지만 연구 대상은 양의 정수이다. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iterate k n`은 n에서 출발하여 정확히 k번 적용한 값이다. -/
def iterate : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterate k (step n)

def ReachesOne (n : ℕ) : Prop := ∃ k, iterate k n = 1

/-- C: 아직 증명되지 않은 전체 콜라츠 추측. -/
def Conjecture : Prop := ∀ n, 0 < n → ReachesOne n

/-- H: 아직 증명되지 않은 전체 하강 명제. -/
def Descent : Prop := ∀ n, 1 < n → ∃ k, 0 < k ∧ 0 < iterate k n ∧ iterate k n < n

theorem step_even {n : ℕ} (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

theorem step_odd {n : ℕ} (h : n % 2 = 1) : step n = 3 * n + 1 := by
  simp [step, h]

/-- L1: 양의 정수는 1회 연산 후에도 양의 정수이다. -/
theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  split <;> omega

/-- L2: 임의의 유한 횟수만큼 반복해도 양수를 유지한다. -/
theorem iterate_pos (k : ℕ) {n : ℕ} (hn : 0 < n) : 0 < iterate k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (step_pos hn)

/-- L3: 먼저 a회, 그 뒤 b회 진행하면 합계 a+b회이다. -/
theorem iterate_add (a b n : ℕ) : iterate (a + b) n = iterate b (iterate a n) := by
  induction a generalizing n with
  | zero => simp only [Nat.zero_add, iterate]
  | succ a ih =>
    simpa only [Nat.succ_add, iterate] using ih (step n)

/-- T1: H를 가정하면 강한 귀납법으로 C를 얻는다. H 자체의 증명은 아니다. -/
theorem conjecture_of_descent (h : Descent) : Conjecture := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      exact ⟨0, rfl⟩
    · obtain ⟨k, _hk, hm, hlt⟩ := h n (by omega)
      -- ih는 모든 양의 m<n에 대해 ReachesOne m을 제공한다.
      obtain ⟨j, hj⟩ := ih (iterate k n) hlt hm
      -- 목표: n에서 1까지 가는 횟수. k+j를 선택하고 두 경로를 잇는다.
      exact ⟨k + j, by rw [iterate_add]; exact hj⟩

/-- T2: C가 참이면 n>1에서 1까지 가는 경로가 곧 하강 경로다. -/
theorem descent_of_conjecture (h : Conjecture) : Descent := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  have hpos : 0 < k := by
    by_contra hnot
    have hz : k = 0 := by omega
    subst k
    simp only [iterate] at hk
    omega
  exact ⟨k, hpos, by rw [hk]; omega, by rw [hk]; exact hn⟩

/-- T3: 핵심 가설은 원래 추측과 동치이며, 난제를 해소한 것이 아니다. -/
theorem conjecture_iff_descent : Conjecture ↔ Descent :=
  ⟨descent_of_conjecture, conjecture_of_descent⟩

/-- D1: 짝수 n>1은 1회 후 하강한다. -/
theorem even_descent {n : ℕ} (hn : 1 < n) (he : n % 2 = 0) :
    0 < iterate 1 n ∧ iterate 1 n < n := by
  simp only [iterate, step_even he]
  omega

/-- D2의 정확한 경로: 4a+1 → 12a+4 → 6a+2 → 3a+1. -/
theorem iterate_three (a : ℕ) : iterate 3 (4 * a + 1) = 3 * a + 1 := by
  have h1 : step (4 * a + 1) = 12 * a + 4 := by
    rw [step_odd (by omega)]; omega
  have h2 : step (12 * a + 4) = 6 * a + 2 := by
    rw [step_even (by omega)]; omega
  have h3 : step (6 * a + 2) = 3 * a + 1 := by
    rw [step_even (by omega)]; omega
  simp only [iterate, h1, h2, h3]

/-- D2: n≡1 (mod 4), n>1이면 3회 후 하강한다. -/
theorem one_mod_four_descent {n : ℕ} (hn : 1 < n) (hr : n % 4 = 1) :
    0 < iterate 3 n ∧ iterate 3 n < n := by
  have heq : n = 4 * (n / 4) + 1 := by omega
  have hit : iterate 3 n = 3 * (n / 4) + 1 := by
    conv_lhs => rw [heq]
    exact iterate_three (n / 4)
  rw [hit]
  omega

/-- D3의 정확한 경로는 한국어 연구 기록에 전개되어 있다. -/
theorem iterate_six (a : ℕ) : iterate 6 (16 * a + 3) = 9 * a + 2 := by
  have h1 : step (16 * a + 3) = 48 * a + 10 := by
    rw [step_odd (by omega)]; omega
  have h2 : step (48 * a + 10) = 24 * a + 5 := by
    rw [step_even (by omega)]; omega
  have h3 : step (24 * a + 5) = 72 * a + 16 := by
    rw [step_odd (by omega)]; omega
  have h4 : step (72 * a + 16) = 36 * a + 8 := by
    rw [step_even (by omega)]; omega
  have h5 : step (36 * a + 8) = 18 * a + 4 := by
    rw [step_even (by omega)]; omega
  have h6 : step (18 * a + 4) = 9 * a + 2 := by
    rw [step_even (by omega)]; omega
  simp only [iterate, h1, h2, h3, h4, h5, h6]

/-- D3: n≡3 (mod 16)이면 6회 후 하강한다. -/
theorem three_mod_sixteen_descent {n : ℕ} (hr : n % 16 = 3) :
    0 < iterate 6 n ∧ iterate 6 n < n := by
  have heq : n = 16 * (n / 16) + 3 := by omega
  have hit : iterate 6 n = 9 * (n / 16) + 2 := by
    conv_lhs => rw [heq]
    exact iterate_six (n / 16)
  rw [hit]
  omega

/-- R: 이번 분류로 아직 해결하지 못한 세 나머지류의 하강 명제. -/
def RemainingDescent : Prop :=
  ∀ n, 1 < n → (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) →
    ∃ k, 0 < k ∧ 0 < iterate k n ∧ iterate k n < n

/-- T4: 남은 나머지류의 하강을 증명하면 H가 완성된다. R은 미해결이다. -/
theorem descent_iff_remaining : Descent ↔ RemainingDescent := by
  constructor
  · intro h n hn _hr
    exact h n hn
  · intro h n hn
    by_cases he : n % 2 = 0
    · exact ⟨1, by decide, even_descent hn he⟩
    by_cases hfour : n % 4 = 1
    · exact ⟨3, by decide, one_mod_four_descent hn hfour⟩
    by_cases hsixteen : n % 16 = 3
    · exact ⟨6, by decide, three_mod_sixteen_descent hsixteen⟩
    exact h n hn (by omega)

/-- T5: 전체 추측과 남은 증명 의무의 정확한 관계. -/
theorem conjecture_iff_remaining : Conjecture ↔ RemainingDescent :=
  conjecture_iff_descent.trans descent_iff_remaining

/-- F1: 매번 감소한다는 더 강한 후보는 거짓이다. -/
theorem not_every_step_descends : ¬ (∀ n, 1 < n → step n < n) := by
  intro h
  have h3 := h 3 (by decide)
  change 10 < 3 at h3
  omega

/-- F2: 모든 시작값이 3회 이내에 하강한다는 후보도 거짓이다. -/
theorem not_every_orbit_descends_within_three :
    ¬ (∀ n, 1 < n → ∃ k, 0 < k ∧ k ≤ 3 ∧ iterate k n < n) := by
  intro h
  obtain ⟨k, hk, hle, hlt⟩ := h 3 (by decide)
  have cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases cases with rfl | rfl | rfl
  · change 10 < 3 at hlt; omega
  · change 5 < 3 at hlt; omega
  · change 16 < 3 at hlt; omega

-- E1: 반복의 정의와 경계값 확인. 모두 커널이 검사하는 구체적인 등식이다.
example : iterate 0 1 = 1 := rfl
example : iterate 3 1 = 1 := rfl
example : iterate 1 2 = 1 := rfl
example : iterate 6 3 = 2 := rfl
example : iterate 7 3 = 1 := rfl
example : iterate 3 5 = 4 := rfl
example : iterate 5 5 = 1 := rfl

-- 미해결 가설이 숨은 공리로 유입되지 않았는지 빌드 출력에서 확인한다.
#print axioms conjecture_iff_descent
#print axioms conjecture_iff_remaining
#print axioms even_descent
#print axioms one_mod_four_descent
#print axioms three_mod_sixteen_descent
#print axioms not_every_step_descends
#print axioms not_every_orbit_descends_within_three

end Collatz
