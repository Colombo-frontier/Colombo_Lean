import Nonsmooth.CircularWideConePolicy

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem circleArc_inner_circleTangent {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (t : ℝ) : ⟪circleArc u v t, circleTangent u v t⟫_ℝ = 0 := by
  have hvu : ⟪v, u⟫_ℝ = 0 := (real_inner_comm u v).trans huv
  simp only [circleArc, circleTangent, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu, hv, huv, hvu]
  ring

def circularNeighborOffset (o u v : E) (r : ℝ) (N : ℕ) (j : ℤ) (x : E) : E :=
  (circularQueryPoint o u v r N j - x) - (r * (1 - Real.cos (circularGridAngle N))) •
    circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))

theorem circular_neighbors_offset_representation (o u v : E) (r : ℝ) (N : ℕ) (j : ℤ) (x : E) :
    circularQueryPoint o u v r N (j - 1) = x + circularNeighborOffset o u v r N j x -
      (r * Real.sin (circularGridAngle N)) •
        circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) ∧
    circularQueryPoint o u v r N (j + 1) = x + circularNeighborOffset o u v r N j x +
      (r * Real.sin (circularGridAngle N)) •
        circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) := by
  constructor
  · rw [circularQueryPoint_neighbor_minus]
    dsimp only [circularNeighborOffset, circularQueryPoint]
    module
  · rw [circularQueryPoint_neighbor_plus]
    dsimp only [circularNeighborOffset, circularQueryPoint]
    module

theorem circularNeighborOffset_orthogonal {o u v x : E} {r : ℝ} {N : ℕ} {j : ℤ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hmove : ⟪circularQueryPoint o u v r N j - x,
      circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))⟫_ℝ = 0) :
    ⟪circularNeighborOffset o u v r N j x,
      circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))⟫_ℝ = 0 := by
  simp only [circularNeighborOffset, inner_sub_left, real_inner_smul_left, hmove,
    circleArc_inner_circleTangent hu hv huv, mul_zero, sub_zero]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem circularNeighborOffset_norm_le {o u v x : E} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hr : 0 ≤ r)
    (N : ℕ) (j : ℤ) :
    ‖circularNeighborOffset o u v r N j x‖ ≤ ‖circularQueryPoint o u v r N j - x‖ +
      (r * Real.sin (circularGridAngle N)) * (2 / (2 : ℝ) ^ N) := by
  have hD := (circularGridAngle_cos_gap_pos N).le
  have hDθ := circularGridAngle_cos_gap_le N
  have hθ := mul_le_mul_of_nonneg_right (circularGridAngle_le_dyadic N)
    (circularGridAngle_sin_pos N).le
  have hgap : r * (1 - Real.cos (circularGridAngle N)) ≤
      (r * Real.sin (circularGridAngle N)) * (2 / (2 : ℝ) ^ N) := by
    have h := mul_le_mul_of_nonneg_left (hDθ.trans hθ) hr
    nlinarith only [h]
  calc
    _ ≤ ‖circularQueryPoint o u v r N j - x‖ +
        ‖(r * (1 - Real.cos (circularGridAngle N))) •
          circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))‖ := norm_sub_le _ _
    _ = ‖circularQueryPoint o u v r N j - x‖ + r * (1 - Real.cos (circularGridAngle N)) := by
      rw [norm_smul, circleArc_norm hu hv huv, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hr hD), mul_one]
    _ ≤ _ := by linarith only [hgap]

theorem circularNeighborOffset_small_of_small_tail {o u v x : E} {r ε : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hr : 0 ≤ r)
    (N : ℕ) (j : ℤ) (hθ : 2 / (2 : ℝ) ^ N ≤ ε / 2)
    (hmove : ‖circularQueryPoint o u v r N j - x‖ ≤
      (r * Real.sin (circularGridAngle N)) * (ε / 2)) :
    ‖circularNeighborOffset o u v r N j x‖ ≤ (r * Real.sin (circularGridAngle N)) * ε := by
  have h := circularNeighborOffset_norm_le (o := o) (x := x) hu hv huv hr N j
  have hm := mul_le_mul_of_nonneg_left hθ (mul_nonneg hr (circularGridAngle_sin_pos N).le)
  nlinarith only [h, hm, hmove]

end
end Nonsmooth
