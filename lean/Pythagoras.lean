import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

namespace Pythagoras

/-- 실수 좌표로 나타낸 평면의 점. -/
abbrev Point := ℝ × ℝ

/-- 두 점 사이의 유클리드 거리의 제곱. -/
def squaredDistance (A B : Point) : ℝ :=
  (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2

/-- 두 점 사이의 유클리드 거리. -/
noncomputable def distance (A B : Point) : ℝ :=
  Real.sqrt (squaredDistance A B)

/-- 벡터 AB와 AC의 내적이 0이다. 비퇴화 삼각형에서는 A가 직각이다.
퇴화한 경우에도 아래의 피타고라스 등식은 성립한다. -/
def RightAngleAt (A B C : Point) : Prop :=
  (B.1 - A.1) * (C.1 - A.1) + (B.2 - A.2) * (C.2 - A.2) = 0

theorem distance_sq (A B : Point) :
    distance A B ^ 2 = squaredDistance A B := by
  unfold distance squaredDistance
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- 좌표 전개에서 교차항은 내적의 두 배이며, 직각 조건으로 사라진다. -/
theorem pythagorean_squared (A B C : Point) (h : RightAngleAt A B C) :
    squaredDistance A B + squaredDistance A C = squaredDistance B C := by
  unfold RightAngleAt at h
  unfold squaredDistance
  calc
    _ = (C.1 - B.1) ^ 2 + (C.2 - B.2) ^ 2 +
        2 * ((B.1 - A.1) * (C.1 - A.1) +
          (B.2 - A.2) * (C.2 - A.2)) := by ring
    _ = _ := by rw [h]; ring

/-- 피타고라스 정리: A가 직각이면 AB² + AC² = BC². -/
theorem pythagorean (A B C : Point) (h : RightAngleAt A B C) :
    distance A B ^ 2 + distance A C ^ 2 = distance B C ^ 2 := by
  rw [distance_sq, distance_sq, distance_sq]
  exact pythagorean_squared A B C h

end Pythagoras
