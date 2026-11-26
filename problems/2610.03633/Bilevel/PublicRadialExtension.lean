import Bilevel.PublicRadialDecay
import Bilevel.PrimitiveGeometry

/-! The actual scalar public radial extension. A unit vector e selects its
normal coordinate; a later specialization takes e to the last coordinate. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PublicRadialExtension
open RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def potential (a R : ℝ) (e z : E) : ℝ := (a/R)*⟪e,z⟫*bowl 1 R z

def gradientField (a R : ℝ) (e z : E) : E :=
  ((a/R)*bowl 1 R z) • e+((a/R)*⟪e,z⟫) • compress R z

def hessianField (a R : ℝ) (e z : E) : E →L[ℝ] E :=
  (a/R) • ((innerSL ℝ (compress R z)).smulRight e+
    (innerSL ℝ e).smulRight (compress R z)+⟪e,z⟫ • compressDerivative R z)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem root_rescale (R : ℝ) (hR : 0<R) (z : E) :
    R*Real.sqrt (1+‖z‖^2/R^2)=Real.sqrt (R^2+‖z‖^2) := by
  apply (sq_eq_sq₀ (mul_nonneg hR.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,root_square,Real.sq_sqrt (by positivity : 0≤R^2+‖z‖^2)]
  field_simp

omit [CompleteSpace E] in
theorem potential_formula (a R : ℝ) (hR : 0<R) (e z : E) :
    potential a R e z=a*⟪e,z⟫*(Real.sqrt (R^2+‖z‖^2)-R) := by
  rw [← root_rescale R hR z]
  unfold potential bowl
  field_simp
  ring

omit [CompleteSpace E] in
theorem bowl_contDiff (R : ℝ) (k : ℕ) : ContDiff ℝ k (bowl (E := E) 1 R) := by
  have hq : ContDiff ℝ k (fun z : E => 1+‖z‖^2/R^2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)
  exact contDiff_const.mul ((hq.sqrt (fun z => (radicand_pos R z).ne')).sub contDiff_const)

omit [CompleteSpace E] in
theorem potential_contDiff (a R : ℝ) (e : E) (k : ℕ) : ContDiff ℝ k (potential a R e) :=
  (contDiff_const.mul (innerSL ℝ e).contDiff).mul (bowl_contDiff R k)

theorem potential_hasGradientAt (a R : ℝ) (hR : 0<R) (e z : E) :
    HasGradientAt (potential a R e) (gradientField a R e z) z := by
  have hb : HasGradientAt (bowl 1 R) (compress R z) z := by
    simpa only [one_mul,compress] using bowl_hasGradientAt 1 R hR z
  have hh := (((innerSL ℝ e).hasFDerivAt (x:=z)).const_mul (a/R)).mul hb.hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1
  ext v
  simp [gradientField,InnerProductSpace.toDual_apply,inner_add_left,real_inner_smul_left]
  ring

theorem potential_gradient (a R : ℝ) (hR : 0<R) (e z : E) :
    gradient (potential a R e) z=gradientField a R e z :=
  (potential_hasGradientAt a R hR e z).gradient

omit [CompleteSpace E] in
theorem gradientField_contDiff (a R : ℝ) (e : E) (k : ℕ) :
    ContDiff ℝ k (gradientField a R e) :=
  ((contDiff_const.mul (bowl_contDiff R k)).smul contDiff_const).add
    ((contDiff_const.mul (innerSL ℝ e).contDiff).smul (compress_contDiff R k))

theorem gradientField_hasFDerivAt (a R : ℝ) (hR : 0<R) (e z : E) :
    HasFDerivAt (gradientField a R e) (hessianField a R e z) z := by
  have hb : HasFDerivAt (bowl 1 R) (innerSL ℝ (compress R z)) z := by
    simpa only [one_mul,compress] using (bowl_hasGradientAt 1 R hR z).hasFDerivAt
  have hh := ((hb.const_mul (a/R)).smul_const e).add
    ((((innerSL ℝ e).hasFDerivAt (x:=z)).const_mul (a/R)).smul (compress_hasFDerivAt R z))
  convert hh using 1
  ext v
  simp [hessianField]
  module

theorem actual_hessian (a R : ℝ) (hR : 0<R) (e z : E) :
    fderiv ℝ (gradient (potential a R e)) z=hessianField a R e z := by
  rw [show gradient (potential a R e)=gradientField a R e from funext (potential_gradient a R hR e)]
  exact (gradientField_hasFDerivAt a R hR e z).fderiv

end Bilevel.PublicRadialExtension
