import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Verification

/-- The identity holds for every pair of real numbers. -/
theorem square_of_sum (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- Without the middle term, the identity fails at a = b = 1. -/
theorem missing_middle_term_counterexample :
    ∃ a b : ℝ, (a + b) ^ 2 ≠ a ^ 2 + b ^ 2 := by
  refine ⟨1, 1, ?_⟩
  norm_num

end Verification
