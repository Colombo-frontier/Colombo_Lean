import Nonsmooth.CircularQueryGrid

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def circularGridAngle (N : ℕ) : ℝ := 2 * Real.pi / (4 * 2 ^ N)

theorem circleArc_add_angle (u v : E) (t s : ℝ) :
    circleArc u v (t + s) = Real.cos s • circleArc u v t + Real.sin s • circleTangent u v t := by
  simp only [circleArc, circleTangent, Real.cos_add, Real.sin_add]
  module

theorem circularQueryPoint_neighbor_plus (o u v : E) (r : ℝ) (N : ℕ) (j : ℤ) :
    circularQueryPoint o u v r N (j + 1) = o + r •
      (Real.cos (circularGridAngle N) • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) +
       Real.sin (circularGridAngle N) • circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))) := by
  have he : 2 * Real.pi * ((j + 1 : ℤ) : ℝ) / (4 * 2 ^ N) =
      2 * Real.pi * (j : ℝ) / (4 * 2 ^ N) + circularGridAngle N := by
    push_cast
    dsimp [circularGridAngle]
    ring
  simp only [circularQueryPoint, he, circleArc_add_angle]

theorem circularQueryPoint_neighbor_minus (o u v : E) (r : ℝ) (N : ℕ) (j : ℤ) :
    circularQueryPoint o u v r N (j - 1) = o + r •
      (Real.cos (circularGridAngle N) • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) -
       Real.sin (circularGridAngle N) • circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))) := by
  have he : 2 * Real.pi * ((j - 1 : ℤ) : ℝ) / (4 * 2 ^ N) =
      2 * Real.pi * (j : ℝ) / (4 * 2 ^ N) + (-circularGridAngle N) := by
    push_cast
    dsimp [circularGridAngle]
    ring
  dsimp only [circularQueryPoint]
  rw [he, circleArc_add_angle, Real.cos_neg, Real.sin_neg]
  simp only [neg_smul, sub_eq_add_neg]

theorem circular_query_cone_coordinates (o u v : E) (r : ℝ) (N : ℕ) (j : ℤ) (a b : ℝ) :
    circularQueryPoint o u v r N j +
      a • (circularQueryPoint o u v r N j - circularQueryPoint o u v r N (j - 1)) +
      b • (circularQueryPoint o u v r N j - circularQueryPoint o u v r N (j + 1)) =
    circularQueryPoint o u v r N j +
      (r * (1 - Real.cos (circularGridAngle N)) * (a + b)) •
        circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) +
      (r * Real.sin (circularGridAngle N) * (a - b)) •
        circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) := by
  rw [circularQueryPoint_neighbor_minus, circularQueryPoint_neighbor_plus]
  dsimp only [circularQueryPoint]
  module

end
end Nonsmooth
