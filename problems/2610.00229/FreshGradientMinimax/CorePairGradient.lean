import FreshGradientMinimax.CoreScalarLipschitz
import FreshGradientMinimax.BlockFunctionGradient

/-! The true two-dimensional gradient of one nonlinear pair, with uniform
norm and Lipschitz estimates. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def corePairGradient (x : Euclid 2) : Euclid 2 :=
  (WithLp.equiv 2 _).symm ![coreLinkTermD1 (x 0) (x 1), coreLinkTermD2 (x 0) (x 1)]

@[simp]
theorem corePairGradient_zero (x : Euclid 2) : corePairGradient x 0 = coreLinkTermD1 (x 0) (x 1) := rfl

@[simp]
theorem corePairGradient_one (x : Euclid 2) : corePairGradient x 1 = coreLinkTermD2 (x 0) (x 1) := rfl

theorem euclid_coordinate_abs_le {m : ℕ} (x : Euclid m) (i : Fin m) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

theorem euclid_two_norm_le (x : Euclid 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [euclid_norm_sq, Fin.sum_univ_two]
  nlinarith only [sq_abs (x 0), sq_abs (x 1), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

theorem corePair_hasFDerivAt (x : Euclid 2) :
    HasFDerivAt (fun y : Euclid 2 => coreLinkTerm (y 0) (y 1)) (innerSL ℝ (corePairGradient x)) x := by
  have h := coreLinkTerm_linear_hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) 0)
    (EuclideanSpace.proj (𝕜 := ℝ) 1) x
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [innerSL_apply, PiLp.inner_apply, RCLike.inner_apply', Fin.sum_univ_two,
    EuclideanSpace.proj, mul_comm]

theorem corePairGradient_coordinate (x : Euclid 2) (i : Fin 2) : |corePairGradient x i| ≤ 96 := by
  fin_cases i
  · exact coreLinkTermD1_bound _ _
  · exact (coreLinkTermD2_bound _ _).trans (by norm_num)

theorem corePairGradient_norm (x : Euclid 2) : ‖corePairGradient x‖ ≤ 102 := by
  have h := euclid_two_norm_le (corePairGradient x)
  simp only [corePairGradient_zero, corePairGradient_one] at h
  linarith only [h, coreLinkTermD1_bound (x 0) (x 1), coreLinkTermD2_bound (x 0) (x 1)]

theorem corePairGradient_difference (x y : Euclid 2) :
    ‖corePairGradient x - corePairGradient y‖ ≤ 3200 * ‖x - y‖ := by
  have h := euclid_two_norm_le (corePairGradient x - corePairGradient y)
  simp only [PiLp.sub_apply, corePairGradient_zero, corePairGradient_one] at h
  have h0 := euclid_coordinate_abs_le (x - y) 0
  have h1 := euclid_coordinate_abs_le (x - y) 1
  simp only [PiLp.sub_apply] at h0 h1
  have hd1 := coreLinkTermD1_sub_le (x 0) (x 1) (y 0) (y 1)
  have hd2 := coreLinkTermD2_sub_le (x 0) (x 1) (y 0) (y 1)
  nlinarith only [h, h0, h1, hd1, hd2, norm_nonneg (x - y)]

end FreshGradientMinimax
