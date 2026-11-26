import Bilevel.SmallGapSmoothness
import Bilevel.SmallGapThirdBounds

/-! Actual third derivative blocks and their integration into Hessian variation. -/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open scoped RealInnerProductSpace
open SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport SmallGapThirdBounds

variable (P : Parameters)

def h000 (ω : ℝ) (y : LowerSpace) : ℝ :=
  -P.μ / P.L *
    (deriv (deriv (deriv (r0 P.S P.R))) (y 0) * normal P.R (y 1) -
      ω * deriv (deriv (deriv (r1 P.S P.δ))) (y 0) * normal P.δ (y 1)) +
    P.μ / P.L ^ 2 * (3 * deriv (P.residual ω) (y 0) * deriv (deriv (P.residual ω)) (y 0) +
      P.residual ω (y 0) * deriv (deriv (deriv (P.residual ω))) (y 0))

def h001 (ω : ℝ) (y : LowerSpace) : ℝ :=
  -P.μ / P.L *
    (deriv (deriv (r0 P.S P.R)) (y 0) * deriv (normal P.R) (y 1) -
      ω * deriv (deriv (r1 P.S P.δ)) (y 0) * deriv (normal P.δ) (y 1))

def h011 (ω : ℝ) (y : LowerSpace) : ℝ :=
  -P.μ / P.L *
    (deriv (r0 P.S P.R) (y 0) * deriv (deriv (normal P.R)) (y 1) -
      ω * deriv (r1 P.S P.δ) (y 0) * deriv (deriv (normal P.δ)) (y 1))

def h111 (ω : ℝ) (y : LowerSpace) : ℝ :=
  -P.μ / P.L *
    (r0 P.S P.R (y 0) * deriv (deriv (deriv (normal P.R))) (y 1) -
      ω * r1 P.S P.δ (y 0) * deriv (deriv (deriv (normal P.δ))) (y 1))

theorem h00_hasFDerivAt (ω : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.h00 ω) ((P.h000 ω y) • p0 + (P.h001 ω y) • p1) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have hr0 := (deriv2_hasDerivAt (r0_contDiff P.S P.R) (y 0)).hasFDerivAt.comp y h0
  have hr1 := (deriv2_hasDerivAt (r1_contDiff P.S P.δ) (y 0)).hasFDerivAt.comp y h0
  have hq0 := ((normal_contDiff P.R P.R_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have hq1 := ((normal_contDiff P.δ P.δ_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have hr := (P.residual_hasDerivAt ω (y 0)).hasFDerivAt.comp y h0
  have hdr := (deriv_hasDerivAt (P.residual_contDiff ω) (y 0)).hasFDerivAt.comp y h0
  have hddr := (deriv2_hasDerivAt (P.residual_contDiff ω) (y 0)).hasFDerivAt.comp y h0
  have h := ((((hr0.mul hq0).sub ((hr1.const_mul ω).mul hq1)).const_mul (P.μ / P.L)).const_sub P.μ).add
    (((hdr.mul hdr).add (hr.mul hddr)).const_mul (P.μ / P.L ^ 2))
  convert h using 1
  · funext v
    simp only [h00, pow_two]
    rfl
  ext v
  simp [h000, h001]
  ring

theorem h01_hasFDerivAt (ω : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.h01 ω) ((P.h001 ω y) • p0 + (P.h011 ω y) • p1) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have hr0 := (deriv_hasDerivAt (r0_contDiff P.S P.R) (y 0)).hasFDerivAt.comp y h0
  have hr1 := (deriv_hasDerivAt (r1_contDiff P.S P.δ) (y 0)).hasFDerivAt.comp y h0
  have hq0 := (deriv_hasDerivAt (normal_contDiff P.R P.R_pos) (y 1)).hasFDerivAt.comp y h1
  have hq1 := (deriv_hasDerivAt (normal_contDiff P.δ P.δ_pos) (y 1)).hasFDerivAt.comp y h1
  have h := (((hr0.mul hq0).sub ((hr1.const_mul ω).mul hq1)).const_mul (-P.μ / P.L))
  convert h using 1
  ext v
  simp [h001, h011]
  ring

theorem h11_hasFDerivAt (ω : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.h11 ω) ((P.h011 ω y) • p0 + (P.h111 ω y) • p1) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have hr0 := ((r0_contDiff P.S P.R).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hr1 := ((r1_contDiff P.S P.δ).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hq0 := (deriv2_hasDerivAt (normal_contDiff P.R P.R_pos) (y 1)).hasFDerivAt.comp y h1
  have hq1 := (deriv2_hasDerivAt (normal_contDiff P.δ P.δ_pos) (y 1)).hasFDerivAt.comp y h1
  have h := (((hr0.mul hq0).sub ((hr1.const_mul ω).mul hq1)).const_mul (P.μ / P.L)).const_sub P.μ
  convert h using 1
  ext v
  simp [h011, h111]
  ring

theorem row_norm_le (a b : ℝ) : ‖a • p0 + b • p1‖ ≤ |a| + |b| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro v
  exact row_abs_bound a b v

theorem coefficient_lipschitz {f : LowerSpace → ℝ} {a b : LowerSpace → ℝ} {D : ℝ}
    (hf : ∀ y, HasFDerivAt f (a y • p0 + b y • p1) y)
    (ha : ∀ y, |a y| ≤ D) (hb : ∀ y, |b y| ≤ D) (y y' : LowerSpace) :
    |f y - f y'| ≤ 2 * D * ‖y - y'‖ := by
  have hnorm (v : LowerSpace) : ‖a v • p0 + b v • p1‖ ≤ 2 * D := by
    have h := row_norm_le (a v) (b v)
    linarith [ha v, hb v]
  exact convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => (hf v).hasFDerivWithinAt) (fun v _ => hnorm v) (Set.mem_univ y') (Set.mem_univ y)

theorem hessian_difference_norm (ω : ℝ) (y y' : LowerSpace) :
    ‖P.lowerYY ω y - P.lowerYY ω y'‖ ≤
      |P.h00 ω y - P.h00 ω y'| + 2 * |P.h01 ω y - P.h01 ω y'| +
        |P.h11 ω y - P.h11 ω y'| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hp : (P.lowerYY ω y - P.lowerYY ω y') v =
      pack ((P.h00 ω y - P.h00 ω y') * v 0 + (P.h01 ω y - P.h01 ω y') * v 1)
        ((P.h01 ω y - P.h01 ω y') * v 0 + (P.h11 ω y - P.h11 ω y') * v 1) 0 := by
    ext i
    fin_cases i <;> simp [P.lowerYY_apply] <;> ring
  rw [hp]
  have hn := pack_norm_le ((P.h00 ω y - P.h00 ω y') * v 0 + (P.h01 ω y - P.h01 ω y') * v 1)
    ((P.h01 ω y - P.h01 ω y') * v 0 + (P.h11 ω y - P.h11 ω y') * v 1) 0
  rw [abs_zero, add_zero] at hn
  have h0 := row_abs_bound (P.h00 ω y - P.h00 ω y') (P.h01 ω y - P.h01 ω y') v
  have h1 := row_abs_bound (P.h01 ω y - P.h01 ω y') (P.h11 ω y - P.h11 ω y') v
  nlinarith

theorem variation_of_third_bounds (ω D : ℝ)
    (h : ∀ y, |P.h000 ω y| ≤ D ∧ |P.h001 ω y| ≤ D ∧
      |P.h011 ω y| ≤ D ∧ |P.h111 ω y| ≤ D) (y y' : LowerSpace) :
    ‖P.lowerYY ω y - P.lowerYY ω y'‖ ≤ 8 * D * ‖y - y'‖ := by
  have h0 := coefficient_lipschitz (P.h00_hasFDerivAt ω)
    (fun v => (h v).1) (fun v => (h v).2.1) y y'
  have h1 := coefficient_lipschitz (P.h01_hasFDerivAt ω)
    (fun v => (h v).2.1) (fun v => (h v).2.2.1) y y'
  have h2 := coefficient_lipschitz (P.h11_hasFDerivAt ω)
    (fun v => (h v).2.2.1) (fun v => (h v).2.2.2) y y'
  have hh := P.hessian_difference_norm ω y y'
  linarith

def thirdSize : ℝ := P.μ / P.L * (2 * C ^ 2 * P.S) +
  P.μ / P.L ^ 2 * (1164 * C ^ 2 * P.S ^ 2 * (P.R + P.δ))

theorem thirdSize_nonneg : 0 ≤ P.thirdSize := by
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  unfold thirdSize
  positivity

theorem actual_third_bounds (ω : ℝ) (hω : |ω| ≤ 1) (y : LowerSpace) :
    |P.h000 ω y| ≤ P.thirdSize ∧ |P.h001 ω y| ≤ P.thirdSize ∧
      |P.h011 ω y| ≤ P.thirdSize ∧ |P.h111 ω y| ≤ P.thirdSize := by
  have h0 := r0_coupling_third_bounds P.S P.R (y 0) (y 1) P.S_pos P.R_pos
  have h1 := r1_coupling_third_bounds P.S P.δ (y 0) (y 1) P.S_pos P.δ_pos
  have hc0 : |deriv (deriv (deriv (r0 P.S P.R))) (y 0) * normal P.R (y 1) -
      ω * deriv (deriv (deriv (r1 P.S P.δ))) (y 0) * normal P.δ (y 1)| ≤ 2 * C ^ 2 * P.S := by
    convert abs_signed_sub_le h0.1 h1.1 hω using 1 <;> ring
  have hc1 : |deriv (deriv (r0 P.S P.R)) (y 0) * deriv (normal P.R) (y 1) -
      ω * deriv (deriv (r1 P.S P.δ)) (y 0) * deriv (normal P.δ) (y 1)| ≤ 2 * C ^ 2 * P.S := by
    convert abs_signed_sub_le h0.2.1 h1.2.1 hω using 1 <;> ring
  have hc2 : |deriv (r0 P.S P.R) (y 0) * deriv (deriv (normal P.R)) (y 1) -
      ω * deriv (r1 P.S P.δ) (y 0) * deriv (deriv (normal P.δ)) (y 1)| ≤ 2 * C ^ 2 * P.S := by
    convert abs_signed_sub_le h0.2.2.1 h1.2.2.1 hω using 1 <;> ring
  have hc3 : |r0 P.S P.R (y 0) * deriv (deriv (deriv (normal P.R))) (y 1) -
      ω * r1 P.S P.δ (y 0) * deriv (deriv (deriv (normal P.δ))) (y 1)| ≤ 2 * C ^ 2 * P.S := by
    convert abs_signed_sub_le h0.2.2.2 h1.2.2.2 hω using 1 <;> ring
  have hμL := div_nonneg P.μ_pos.le P.L_pos.le
  have hμL2 := div_nonneg P.μ_pos.le (sq_nonneg P.L)
  have hcomp : 0 ≤ P.μ / P.L ^ 2 * (1164 * C ^ 2 * P.S ^ 2 * (P.R + P.δ)) := by
    have hR := P.R_pos
    have hδ := P.δ_pos
    exact mul_nonneg hμL2 (by positivity)
  have hmul {a : ℝ} (ha : |a| ≤ 2 * C ^ 2 * P.S) : |-P.μ / P.L * a| ≤ P.thirdSize := by
    rw [abs_mul, neg_div, abs_neg, abs_of_nonneg hμL]
    exact (mul_le_mul_of_nonneg_left ha hμL).trans (le_add_of_nonneg_right hcomp)
  constructor
  · have hr := P.compensation_third_bound ω (y 0) hω
    have hb0 := mul_le_mul_of_nonneg_left hc0 hμL
    have hb1 := mul_le_mul_of_nonneg_left hr hμL2
    unfold h000
    refine (abs_add _ _).trans ?_
    rw [abs_mul, neg_div, abs_neg, abs_of_nonneg hμL, abs_mul, abs_of_nonneg hμL2]
    exact add_le_add hb0 hb1
  exact ⟨hmul hc1, hmul hc2, hmul hc3⟩

theorem hessian_variation_y (ω : ℝ) (hω : |ω| ≤ 1) (y y' : LowerSpace) :
    ‖P.lowerYY ω y - P.lowerYY ω y'‖ ≤ 8 * P.thirdSize * ‖y - y'‖ :=
  P.variation_of_third_bounds ω P.thirdSize (P.actual_third_bounds ω hω) y y'

theorem lowerYY_differentiable (ω : ℝ) : Differentiable ℝ (P.lowerYY ω) := by
  intro y
  have h0 := P.h00_hasFDerivAt ω y
  have h1 := P.h01_hasFDerivAt ω y
  have h2 := P.h11_hasFDerivAt ω y
  have h := ((((h0.smul_const (p0.smulRight e0)).add (h1.smul_const (p1.smulRight e0))).add
    (h1.smul_const (p0.smulRight e1))).add (h2.smul_const (p1.smulRight e1))).add_const
      (P.L • p2.smulRight e2)
  convert h.differentiableAt using 1
  funext v
  ext w i
  simp [lowerYY]
  ring

/-- The derivative of the actual lower Hessian is bounded in operator norm. -/
theorem lowerYY_derivative_bound (ω : ℝ) (hω : |ω| ≤ 1) (y : LowerSpace) :
    ‖fderiv ℝ (P.lowerYY ω) y‖ ≤ 8 * P.thirdSize := by
  have hlip : LipschitzWith ⟨8 * P.thirdSize, mul_nonneg (by norm_num) P.thirdSize_nonneg⟩
      (P.lowerYY ω) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro v w
    exact P.hessian_variation_y ω hω v w
  exact norm_fderiv_le_of_lipschitz ℝ hlip

/-- The raw numerical Hessian-variation budget has the source scale `μ θ`. -/
def rawRho : ℝ := 18640 * C ^ 2 * P.μ * (P.S / P.L)

theorem rawRho_nonneg : 0 ≤ P.rawRho := by
  have hμ := P.μ_pos
  have hS := P.S_pos
  have hL := P.L_pos
  unfold rawRho
  positivity

theorem thirdSize_scale (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    8 * P.thirdSize ≤ P.rawRho := by
  have hC2 : 1 ≤ C ^ 2 := by nlinarith [C_one_le]
  have hS := P.S_pos
  have hR := P.R_pos
  have hL := P.L_pos
  have hμ := P.μ_pos
  have hδ := P.δ_pos
  have hmul := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ P.S * P.R by positivity)
  have hSR : P.S * P.R ≤ P.L := by nlinarith
  have hδR := mul_le_mul_of_nonneg_left P.delta_le_R P.S_pos.le
  have hratio : P.S / P.L * (P.R + P.δ) ≤ 2 := by
    have hdiv : (P.S * (P.R + P.δ)) / P.L ≤ 2 :=
      (div_le_iff₀ hL).mpr (by nlinarith)
    convert hdiv using 1
    ring
  have hb := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ 1164 * C ^ 2 * P.μ * (P.S / P.L) by positivity)
  dsimp [thirdSize, rawRho]
  ring_nf at hb ⊢
  nlinarith

theorem hessian_variation_joint (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L)
    (x x' : ℝ) (y y' : LowerSpace) :
    ‖P.lowerYY ω y - P.lowerYY ω y'‖ ≤ P.rawRho * Model.jointDistance x x' y y' := by
  have hy : ‖y - y'‖ ≤ Model.jointDistance x x' y y' := by
    unfold Model.jointDistance
    have hn : 0 ≤ ‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2),
      sq_nonneg ‖x - x'‖, norm_nonneg (y - y')]
  exact (P.hessian_variation_y ω hω y y').trans
    ((mul_le_mul_of_nonneg_right (P.thirdSize_scale hscale) (norm_nonneg (y - y'))).trans
      (mul_le_mul_of_nonneg_left hy P.rawRho_nonneg))

end Bilevel.SmallGapInstance.Parameters
