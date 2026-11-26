import Bilevel.SmallGapInstanceBounds

/-! Global first-order smoothness budgets of the actual clipped small-gap lift. -/

noncomputable section
namespace Bilevel.SmallGapInstance

open scoped RealInnerProductSpace
open SmallGapLiftSupport

theorem coord_abs_le_norm (v : LowerSpace) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have hn := norm_sq v
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  have hnorm := norm_nonneg v
  fin_cases i <;> dsimp <;> nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
    abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2)]

theorem pack_norm_le (a b c : ℝ) : ‖pack a b c‖ ≤ |a| + |b| + |c| := by
  have h0 := norm_add_le (a • e0 + b • e1) (c • e2)
  have h1 := norm_add_le (a • e0) (b • e1)
  simp only [norm_smul, Real.norm_eq_abs, e0, e1, e2, EuclideanSpace.norm_single,
    norm_one, mul_one] at h0 h1
  exact h0.trans (add_le_add_right h1 _)

theorem row_abs_bound (a b : ℝ) (v : LowerSpace) :
    |a * v 0 + b * v 1| ≤ (|a| + |b|) * ‖v‖ := by
  have h0 := mul_le_mul_of_nonneg_left (coord_abs_le_norm v 0) (abs_nonneg a)
  have h1 := mul_le_mul_of_nonneg_left (coord_abs_le_norm v 1) (abs_nonneg b)
  have h := abs_add (a * v 0) (b * v 1)
  rw [abs_mul, abs_mul] at h
  nlinarith

namespace Parameters
variable (P : Parameters)

def baseHessian : LowerSpace →L[ℝ] LowerSpace :=
  (P.μ • p0).smulRight e0 + (P.μ • p1).smulRight e1 + (P.L • p2).smulRight e2

theorem baseHessian_apply (v : LowerSpace) :
    P.baseHessian v = pack (P.μ * v 0) (P.μ * v 1) (P.L * v 2) := by
  simp [baseHessian, pack]

theorem baseHessian_norm_le : ‖P.baseHessian‖ ≤ P.L := by
  apply ContinuousLinearMap.opNorm_le_bound _ P.L_pos.le
  intro v
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hs : P.μ ^ 2 ≤ P.L ^ 2 := by nlinarith [P.μ_le_L]
  have h0 := mul_le_mul_of_nonneg_right hs (sq_nonneg (v 0))
  have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg (v 1))
  have he := norm_sq (P.baseHessian v)
  have hv0 : (P.baseHessian v) 0 = P.μ * v 0 := by rw [P.baseHessian_apply, pack_zero]
  have hv1 : (P.baseHessian v) 1 = P.μ * v 1 := by rw [P.baseHessian_apply, pack_one]
  have hv2 : (P.baseHessian v) 2 = P.L * v 2 := by rw [P.baseHessian_apply, pack_two]
  rw [hv0, hv1, hv2] at he
  have hv := norm_sq v
  have hvL := congrArg (fun r : ℝ => P.L ^ 2 * r) hv
  dsimp at hvL
  have hsq : ‖P.baseHessian v‖ ^ 2 ≤ (P.L * ‖v‖) ^ 2 := by nlinarith only [h0, h1, he, hvL]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg v))).mp hsq

theorem hessian_perturbation_norm (ω : ℝ) (y : LowerSpace) (hω : |ω| ≤ 1) :
    ‖P.lowerYY ω y - P.baseHessian‖ ≤ 4 * P.hessianPerturbation := by
  have hE := P.hessianPerturbation_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he := P.hessian_entry_bounds ω y hω
  have h0 := row_abs_bound (P.h00 ω y - P.μ) (P.h01 ω y) v
  have h1 := row_abs_bound (P.h01 ω y) (P.h11 ω y - P.μ) v
  have hh0 := mul_le_mul_of_nonneg_right (add_le_add he.1 he.2.1) (norm_nonneg v)
  have hh1 := mul_le_mul_of_nonneg_right (add_le_add he.2.1 he.2.2) (norm_nonneg v)
  have hp : (P.lowerYY ω y - P.baseHessian) v =
      pack ((P.h00 ω y - P.μ) * v 0 + P.h01 ω y * v 1)
        (P.h01 ω y * v 0 + (P.h11 ω y - P.μ) * v 1) 0 := by
    ext i
    fin_cases i <;> simp [P.lowerYY_apply, P.baseHessian_apply, pack_zero, pack_one, pack_two] <;> ring
  rw [hp]
  have hb := pack_norm_le ((P.h00 ω y - P.μ) * v 0 + P.h01 ω y * v 1)
    (P.h01 ω y * v 0 + (P.h11 ω y - P.μ) * v 1) 0
  rw [abs_zero, add_zero] at hb
  nlinarith

theorem lowerYY_norm_le (ω : ℝ) (y : LowerSpace) (hω : |ω| ≤ 1)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) : ‖P.lowerYY ω y‖ ≤ 2 * P.L := by
  have hb := P.baseHessian_norm_le
  have hp := P.hessian_perturbation_norm ω y hω
  have ht := norm_sub_le_norm_sub_add_norm_sub (P.lowerYY ω y) P.baseHessian 0
  simp only [sub_zero] at ht
  nlinarith [P.μ_le_L]

theorem lowerY_lipschitz_y (ω x : ℝ) (hω : |ω| ≤ 1)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) (y y' : LowerSpace) :
    ‖P.lowerY ω x y - P.lowerY ω x y'‖ ≤ 2 * P.L * ‖y - y'‖ := by
  exact convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => (P.lowerY_hasFDerivAt ω x v).hasFDerivWithinAt)
    (fun v _ => P.lowerYY_norm_le ω v hω hsmall) (Set.mem_univ y') (Set.mem_univ y)

theorem lowerY_difference_x (ω x x' : ℝ) (y : LowerSpace) :
    P.lowerY ω x y - P.lowerY ω x' y = (-P.L * (x - x')) • e0 := by
  ext i
  fin_cases i <;> simp [lowerY, lowerU, lowerS, e0]
  ring

theorem lowerY_lipschitz_joint (ω x x' : ℝ) (hω : |ω| ≤ 1)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) (y y' : LowerSpace) :
    ‖P.lowerY ω x y - P.lowerY ω x' y'‖ ≤ 2 * P.L * ‖y - y'‖ + P.L * ‖x - x'‖ := by
  have hy := P.lowerY_lipschitz_y ω x hω hsmall y y'
  have hx : ‖P.lowerY ω x y' - P.lowerY ω x' y'‖ = P.L * ‖x - x'‖ := by
    rw [P.lowerY_difference_x]
    simp [norm_smul, e0, abs_mul, abs_of_pos P.L_pos]
  exact (norm_sub_le_norm_sub_add_norm_sub (P.lowerY ω x y) (P.lowerY ω x y') (P.lowerY ω x' y')).trans
    (add_le_add hy hx.le)

theorem lower_smooth (ω : ℝ) (hω : |ω| ≤ 1)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) (x x' : ℝ) (y y' : LowerSpace) :
    ‖P.lowerX ω x y - P.lowerX ω x' y'‖ ^ 2 +
      ‖P.lowerY ω x y - P.lowerY ω x' y'‖ ^ 2 ≤
      (3 * P.L) ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  have hL := P.L_pos
  have hdx := norm_nonneg (x - x')
  have hdy := norm_nonneg (y - y')
  have hy := P.lowerY_lipschitz_joint ω x x' hω hsmall y y'
  have hx : ‖P.lowerX ω x y - P.lowerX ω x' y'‖ ≤ P.L * ‖y - y'‖ := by
    have he : P.lowerX ω x y - P.lowerX ω x' y' = -P.L * ((y - y') 0) := by
      simp only [lowerX, PiLp.sub_apply]
      ring
    rw [he, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left (coord_abs_le_norm (y - y') 0) hL.le
  have hx2 : ‖P.lowerX ω x y - P.lowerX ω x' y'‖ ^ 2 ≤ P.L ^ 2 * ‖y - y'‖ ^ 2 := by
    nlinarith [norm_nonneg (P.lowerX ω x y - P.lowerX ω x' y')]
  have hy2 : ‖P.lowerY ω x y - P.lowerY ω x' y'‖ ^ 2 ≤
      (2 * P.L * ‖y - y'‖ + P.L * ‖x - x'‖) ^ 2 := by
    nlinarith [norm_nonneg (P.lowerY ω x y - P.lowerY ω x' y')]
  nlinarith [sq_nonneg (2 * P.L * ‖y - y'‖ - P.L * ‖x - x'‖),
    mul_nonneg (sq_nonneg P.L) (sq_nonneg ‖x - x'‖)]

theorem upperY_norm (x : ℝ) (y : LowerSpace) : ‖P.upperY x y‖ = P.L := by
  simp [upperY, pack, norm_smul, e1, abs_of_pos P.L_pos]

theorem upper_gradient_bound (x : ℝ) (y : LowerSpace) :
    ‖P.upperX x y‖ ^ 2 + ‖P.upperY x y‖ ^ 2 ≤ 2 * P.L ^ 2 := by
  have hs := Bowl.slope_bound P.L x P.L_pos.le
  rw [P.upperY_norm]
  change |Bowl.slope P.L x| ^ 2 + P.L ^ 2 ≤ _
  nlinarith [abs_nonneg (Bowl.slope P.L x), P.L_pos]

theorem upper_smooth (x x' : ℝ) (y y' : LowerSpace) :
    ‖P.upperX x y - P.upperX x' y'‖ ^ 2 + ‖P.upperY x y - P.upperY x' y'‖ ^ 2 ≤
      P.L ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  have hlip : LipschitzWith ⟨P.L, P.L_pos.le⟩ (Bowl.slope P.L) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (Bowl.hasDerivAt_slope P.L t).differentiableAt)
    intro t
    have hb := Bowl.curvature_bounds P.L t P.L_pos
    change |deriv (Bowl.slope P.L) t| ≤ P.L
    rw [abs_of_pos hb.1]
    exact hb.2
  have h := hlip.dist_le_mul x x'
  simp only [Real.dist_eq, NNReal.coe_mk] at h
  simp only [upperX, upperY, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  have he : |Bowl.slope P.L x - Bowl.slope P.L x'| ^ 2 ≤ P.L ^ 2 * |x - x'| ^ 2 := by
    nlinarith [abs_nonneg (Bowl.slope P.L x - Bowl.slope P.L x'), abs_nonneg (x - x'), P.L_pos]
  simp only [Real.norm_eq_abs]
  nlinarith [mul_nonneg (sq_nonneg P.L) (sq_nonneg ‖y - y'‖)]

end Parameters
end Bilevel.SmallGapInstance
