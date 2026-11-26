import Bilevel.CompensatedMeanHessian

/-! Assembly of the actual mean objectives into Model.Primitive from proved
analytic budgets. No derivative field is supplied independently of its
displayed scalar objective. -/

noncomputable section
namespace Bilevel.CompensatedMean
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem pack_first_norm (u : E) : ‖pack E u 0 0‖ = ‖u‖ := by
  have h := pack_norm_sq u 0 0
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

namespace Data
variable (P : Data (E := E))

theorem lowerY_difference_x (x x' : E) (y : LowerSpace E) :
    P.lowerY x y-P.lowerY x' y = pack E ((-P.L) • (x-x')) 0 0 := by
  apply pack_ext
  · simp only [lowerY,map_sub,uProj_pack,smul_sub]
    module
  · simp only [lowerY,map_sub,sProj_pack,sub_self]
  · simp only [lowerY,map_sub,zProj_pack,sub_self]

theorem lowerY_lipschitz_joint (hμ : 0 ≤ P.μ) (hμL : P.μ ≤ P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2)
    (x x' : E) (y y' : LowerSpace E) :
    ‖P.lowerY x y-P.lowerY x' y'‖ ≤ 2*P.L*‖y-y'‖+P.L*‖x-x'‖ := by
  have hL := hμ.trans hμL
  have hy := P.lowerY_lipschitz_y hμ hμL hpert x y y'
  have hx : ‖P.lowerY x y'-P.lowerY x' y'‖ = P.L*‖x-x'‖ := by
    rw [P.lowerY_difference_x,pack_first_norm,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hL]
  exact (norm_sub_le_norm_sub_add_norm_sub (P.lowerY x y) (P.lowerY x y') (P.lowerY x' y')).trans
    (add_le_add hy hx.le)

theorem lower_smooth (hμ : 0 ≤ P.μ) (hμL : P.μ ≤ P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2)
    (x x' : E) (y y' : LowerSpace E) :
    ‖P.lowerX x y-P.lowerX x' y'‖^2+‖P.lowerY x y-P.lowerY x' y'‖^2 ≤
      (3*P.L)^2*(‖x-x'‖^2+‖y-y'‖^2) := by
  have hL := hμ.trans hμL
  have hdx := norm_nonneg (x-x')
  have hdy := norm_nonneg (y-y')
  have hy := P.lowerY_lipschitz_joint hμ hμL hpert x x' y y'
  have hx : ‖P.lowerX x y-P.lowerX x' y'‖ ≤ P.L*‖y-y'‖ := by
    change ‖(-P.L) • uProj E y-(-P.L) • uProj E y'‖ ≤ _
    rw [← smul_sub,← map_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left (uProj_norm_le (y-y')) hL
  have hx2 : ‖P.lowerX x y-P.lowerX x' y'‖^2 ≤ P.L^2*‖y-y'‖^2 := by
    nlinarith [norm_nonneg (P.lowerX x y-P.lowerX x' y')]
  have hy2 : ‖P.lowerY x y-P.lowerY x' y'‖^2 ≤ (2*P.L*‖y-y'‖+P.L*‖x-x'‖)^2 := by
    nlinarith [norm_nonneg (P.lowerY x y-P.lowerY x' y')]
  nlinarith [sq_nonneg (2*P.L*‖y-y'‖-P.L*‖x-x'‖),mul_nonneg (sq_nonneg P.L) (sq_nonneg ‖x-x'‖)]

theorem upperY_difference (x x' : E) (y y' : LowerSpace E) :
    P.upperY x y-P.upperY x' y' = pack E (gradient P.A (uProj E y)-gradient P.A (uProj E y')) 0 0 := by
  apply pack_ext <;> simp only [upperY,map_sub,uProj_pack,sProj_pack,zProj_pack,sub_self]

theorem upper_smooth (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hA : ∀ u v,‖gradient P.A u-gradient P.A v‖ ≤ Lf*‖u-v‖)
    (x x' : E) (y y' : LowerSpace E) :
    ‖P.upperX x y-P.upperX x' y'‖^2+‖P.upperY x y-P.upperY x' y'‖^2 ≤
      Lf^2*(‖x-x'‖^2+‖y-y'‖^2) := by
  rw [P.upperY_difference,pack_first_norm]
  simp only [upperX,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add]
  have hh := hA (uProj E y) (uProj E y')
  rw [← map_sub] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left (uProj_norm_le (y-y')) hLf)
  have hs : ‖gradient P.A (uProj E y)-gradient P.A (uProj E y')‖^2 ≤ Lf^2*‖y-y'‖^2 := by
    nlinarith [norm_nonneg (gradient P.A (uProj E y)-gradient P.A (uProj E y')),norm_nonneg (y-y')]
  nlinarith [mul_nonneg (sq_nonneg Lf) (sq_nonneg ‖x-x'‖)]

theorem lowerYY_variation_joint (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hthird : ∀ y,‖iteratedFDeriv ℝ 3 P.perturbation y‖ ≤ ρ)
    (x x' : E) (y y' : LowerSpace E) :
    ‖P.lowerYY y-P.lowerYY y'‖ ≤ ρ*Model.jointDistance x x' y y' := by
  have hy : ‖y-y'‖ ≤ Model.jointDistance x x' y y' := by
    unfold Model.jointDistance
    have hn : 0 ≤ ‖x-x'‖^2+‖y-y'‖^2 := by positivity
    nlinarith [Real.sq_sqrt hn,Real.sqrt_nonneg (‖x-x'‖^2+‖y-y'‖^2),
      sq_nonneg ‖x-x'‖,norm_nonneg (y-y')]
  exact (P.lowerYY_variation ρ hthird y y').trans (mul_le_mul_of_nonneg_left hy hρ)

def primitive (hμ : 0 < P.μ) (hμL : P.μ ≤ P.L) (Lf Cf ρ : ℝ)
    (hLf : 0 ≤ Lf) (hCf : 0 ≤ Cf) (hρ : 0 ≤ ρ)
    (hA : ∀ u v,‖gradient P.A u-gradient P.A v‖ ≤ Lf*‖u-v‖)
    (hupper : ∀ x y,‖P.upperY x y‖ ≤ Cf)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2)
    (hthird : ∀ y,‖iteratedFDeriv ℝ 3 P.perturbation y‖ ≤ ρ) :
    Model.Primitive (X := E) (Y := LowerSpace E) (P.μ/2) Lf (3*P.L) Cf ρ where
  μ_pos := by positivity
  Lf_nonneg := hLf
  Lg_nonneg := mul_nonneg (by norm_num) (hμ.le.trans hμL)
  Cf_nonneg := hCf
  ρ_nonneg := hρ
  f := P.upper
  g := P.lower
  fx := P.upperX
  fy := P.upperY
  gx := P.lowerX
  gy := P.lowerY
  gyy := fun _ => P.lowerYY
  gxy := fun _ _ => P.lowerXY
  has_fx := P.upper_hasGradientX
  has_fy := P.upper_hasGradientY
  has_gx := P.lower_hasGradientX
  has_gy := P.lower_hasGradientY
  has_gyy := P.lowerY_hasFDerivAt
  has_gxy := P.lowerX_hasFDerivAt
  strong_convex := P.lower_strong_convex hμ hμL hpert
  upper_bound := hupper
  smooth_f := P.upper_smooth Lf hLf hA
  smooth_g := P.lower_smooth hμ.le hμL hpert
  variation_yy := P.lowerYY_variation_joint ρ hρ hthird
  variation_xy := by
    intro x x' y y'
    simp only [sub_self,norm_zero]
    exact mul_nonneg hρ (Real.sqrt_nonneg _)

end Data
end Bilevel.CompensatedMean
