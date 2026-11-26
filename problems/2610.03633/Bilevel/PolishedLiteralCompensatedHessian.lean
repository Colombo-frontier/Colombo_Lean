import Bilevel.GradientJetBounds
import Bilevel.PolishedLiteralCompensatedCore

/-! Actual Hessian of the clipped mean lift and its global lower/smoothness
bounds. The dummy block is included in the Euclidean coercivity argument. -/

noncomputable section
namespace Bilevel.PolishedLiteralCompensated
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Data
variable (P : Data (E := E))

def baseHessian : LowerSpace E →L[ℝ] LowerSpace E :=
  P.μ • ContinuousLinearMap.id ℝ (LowerSpace E)+(P.L-P.μ) • (zProj E).smulRight (pack E 0 0 1)

def lowerYY (y : LowerSpace E) : LowerSpace E →L[ℝ] LowerSpace E :=
  P.baseHessian+fderiv ℝ (gradient P.perturbation) y

def lowerXY : LowerSpace E →L[ℝ] E := (-P.L) • uProj E

omit [CompleteSpace E] in
theorem baseHessian_apply (v : LowerSpace E) :
    P.baseHessian v = pack E (P.μ • uProj E v) (P.μ*sProj E v) (P.L*zProj E v) := by
  apply pack_ext
  · simp [baseHessian]
  · simp [baseHessian]
  · simp [baseHessian]
    ring

theorem lowerY_decomposition (x : E) (y : LowerSpace E) :
    P.lowerY x y = P.baseHessian y-pack E (P.L • x) 0 0+gradient P.perturbation y := by
  rw [(P.perturbation_hasGradientAt y).gradient,P.baseHessian_apply]
  apply pack_ext <;> simp only [lowerY,perturbationGradient,map_add,map_sub,uProj_pack,sProj_pack,zProj_pack,
    sub_zero,add_zero]

theorem lowerY_hasFDerivAt (x : E) (y : LowerSpace E) :
    HasFDerivAt (P.lowerY x) (P.lowerYY y) y := by
  have he : P.lowerY x = fun v => P.baseHessian v-pack E (P.L • x) 0 0+gradient P.perturbation v :=
    funext (P.lowerY_decomposition x)
  rw [he]
  exact ((P.baseHessian.hasFDerivAt.sub_const _).add
    ((GradientJetBounds.gradient_contDiff P.perturbation_contDiff).differentiable (by norm_num) y).hasFDerivAt)

omit [CompleteSpace E] in
theorem lowerX_hasFDerivAt (x : E) (y : LowerSpace E) :
    HasFDerivAt (P.lowerX x) P.lowerXY y := (uProj E).hasFDerivAt.const_smul (-P.L)

omit [CompleteSpace E] in
theorem baseHessian_norm_bound (hμ : 0 ≤ P.μ) (hμL : P.μ ≤ P.L) : ‖P.baseHessian‖ ≤ P.L := by
  have hL : 0 ≤ P.L := hμ.trans hμL
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro v
  rw [P.baseHessian_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg v))).mp
  rw [pack_norm_sq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ]
  simp only [mul_pow]
  rw [lower_norm_sq]
  have hs : P.μ^2 ≤ P.L^2 := (sq_le_sq₀ hμ hL).mpr hμL
  have h0 := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖uProj E v‖)
  have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg (sProj E v))
  nlinarith only [h0,h1]

omit [CompleteSpace E] in
theorem baseHessian_coercive (hμL : P.μ ≤ P.L) (v : LowerSpace E) :
    P.μ*‖v‖^2 ≤ ⟪P.baseHessian v,v⟫ := by
  rw [P.baseHessian_apply,inner_pack,real_inner_smul_left,real_inner_self_eq_norm_sq,lower_norm_sq]
  have hh := mul_le_mul_of_nonneg_right hμL (sq_nonneg (zProj E v))
  nlinarith only [hh]

theorem lowerYY_coercive (_hμ : 0 < P.μ) (hμL : P.μ ≤ P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2) (y v : LowerSpace E) :
    (P.μ/2)*‖v‖^2 ≤ ⟪P.lowerYY y v,v⟫ := by
  have hp : ‖fderiv ℝ (gradient P.perturbation) y‖ ≤ P.μ/2 :=
    (GradientJetBounds.hessian_norm_eq P.perturbation_contDiff y).le.trans (hpert y)
  have ha : ‖fderiv ℝ (gradient P.perturbation) y v‖ ≤ (P.μ/2)*‖v‖ :=
    ((fderiv ℝ (gradient P.perturbation) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg v))
  have hi : |⟪fderiv ℝ (gradient P.perturbation) y v,v⟫| ≤ (P.μ/2)*‖v‖^2 :=
    (abs_real_inner_le_norm _ v).trans ((mul_le_mul_of_nonneg_right ha (norm_nonneg v)).trans_eq (by ring))
  have hb := P.baseHessian_coercive hμL v
  change (P.μ/2)*‖v‖^2 ≤ ⟪P.baseHessian v+fderiv ℝ (gradient P.perturbation) y v,v⟫
  rw [inner_add_left]
  linarith [(abs_le.mp hi).1]

theorem lower_strong_convex (hμ : 0 < P.μ) (hμL : P.μ ≤ P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2) (x : E) (u v : LowerSpace E) :
    P.lower x u+⟪P.lowerY x u,v-u⟫+(P.μ/2)/2*‖v-u‖^2 ≤ P.lower x v :=
  HessianLowerBound.first_order_lower (P.lower_hasGradientY x) (P.lowerY_hasFDerivAt x)
    (P.lowerYY_coercive hμ hμL hpert) u v

theorem lowerYY_norm_bound (hμ : 0 ≤ P.μ) (hμL : P.μ ≤ P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2) (y : LowerSpace E) :
    ‖P.lowerYY y‖ ≤ 2*P.L := by
  have hp : ‖fderiv ℝ (gradient P.perturbation) y‖ ≤ P.μ/2 :=
    (GradientJetBounds.hessian_norm_eq P.perturbation_contDiff y).le.trans (hpert y)
  have hb := P.baseHessian_norm_bound hμ hμL
  have hh := norm_add_le P.baseHessian (fderiv ℝ (gradient P.perturbation) y)
  change ‖P.baseHessian+fderiv ℝ (gradient P.perturbation) y‖ ≤ _
  linarith

theorem lowerY_lipschitz_y (hμ : 0 ≤ P.μ) (hμL : P.μ ≤ P.L)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2) (x : E) (y y' : LowerSpace E) :
    ‖P.lowerY x y-P.lowerY x y'‖ ≤ (2*P.L)*‖y-y'‖ :=
  convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => (P.lowerY_hasFDerivAt x v).hasFDerivWithinAt)
    (fun v _ => P.lowerYY_norm_bound hμ hμL hpert v) (Set.mem_univ y') (Set.mem_univ y)

theorem lowerYY_variation (ρ : ℝ)
    (hthird : ∀ y,‖iteratedFDeriv ℝ 3 P.perturbation y‖ ≤ ρ) (y y' : LowerSpace E) :
    ‖P.lowerYY y-P.lowerYY y'‖ ≤ ρ*‖y-y'‖ := by
  have he : P.lowerYY y-P.lowerYY y' =
      fderiv ℝ (gradient P.perturbation) y-fderiv ℝ (gradient P.perturbation) y' := by
    dsimp [lowerYY]
    abel
  rw [he]
  exact GradientJetBounds.hessian_lipschitz P.perturbation_contDiff ρ hthird y y'

theorem response_minimizes (hμ : 0 < P.μ) (hμL : P.μ ≤ P.L) (hL : P.L ≠ 0)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2)
    (hcore : ∀ u j,j ≤ P.J → |P.r u/P.L| ≤ P.w j/4) (x : E) (y : LowerSpace E) :
    P.lower x (P.response x) ≤ P.lower x y := by
  have hh := P.lower_strong_convex hμ hμL hpert x (P.response x) y
  rw [P.response_stationary x hμ.ne' hL hcore,inner_zero_left,add_zero] at hh
  have hn : 0 ≤ (P.μ/2)/2*‖y-P.response x‖^2 := by positivity
  linarith

theorem response_unique (hμ : 0 < P.μ) (hμL : P.μ ≤ P.L) (hL : P.L ≠ 0)
    (hpert : ∀ y,‖iteratedFDeriv ℝ 2 P.perturbation y‖ ≤ P.μ/2)
    (hcore : ∀ u j,j ≤ P.J → |P.r u/P.L| ≤ P.w j/4) (x : E) (y : LowerSpace E)
    (hy : P.lower x y ≤ P.lower x (P.response x)) : y = P.response x := by
  have hh := P.lower_strong_convex hμ hμL hpert x (P.response x) y
  rw [P.response_stationary x hμ.ne' hL hcore,inner_zero_left,add_zero] at hh
  have hn : ‖y-P.response x‖^2 ≤ 0 := by nlinarith
  have hz : ‖y-P.response x‖ = 0 := by nlinarith [norm_nonneg (y-P.response x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Data
end Bilevel.PolishedLiteralCompensated
