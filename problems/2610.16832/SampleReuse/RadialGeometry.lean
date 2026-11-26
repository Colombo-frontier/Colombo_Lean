import SampleReuse.RadialProfiles
import RandomizedFO2003.GradientCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus

open RandomizedFO2003.Calculus
open scoped InnerProductSpace Topology

namespace SampleReuse
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem norm_hasFDerivAt_inner {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
  convert hn using 1
  · funext y
    exact (Real.sqrt_sq (norm_nonneg y)).symm
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]
    field_simp
    ring

theorem scalar_norm_hasGradientAt {f : ℝ → ℝ} {a : ℝ} {x : E}
    (hx : x ≠ 0) (hf : HasDerivAt f a ‖x‖) :
    HasGradientAt (fun y : E => f ‖y‖) ((a/‖x‖) • x) x := by
  apply hasGradientAt_of_pairing (hf.comp_hasFDerivAt x (norm_hasFDerivAt_inner hx))
  intro v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, real_inner_smul_left, smul_eq_mul]
  ring

omit [CompleteSpace E] in
theorem radial_norm_contDiff {f : ℝ → ℝ} {a c : ℝ} (ha : 0 < a)
    (hf : ∀ n : ℕ∞, ContDiff ℝ n f) (hflat : ∀ r, r ≤ a → f r = c)
    (n : ℕ∞) : ContDiff ℝ n (fun x : E => f ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := c)).congr_of_eventuallyEq
    have he : ∀ᶠ y : E in 𝓝 0, ‖y‖ < a :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using ha))
    exact he.mono (fun y hy => hflat ‖y‖ hy.le)
  · exact (hf n).contDiffAt.comp x (contDiffAt_norm ℝ hx)

def radialWallLoss (b R : ℝ) (x : E) : ℝ := radialWall b R ‖x‖
def radialCutoffLoss (R : ℝ) (x : E) : ℝ := radialCutoff (‖x‖/R)
def radialGlobalization (f : E → ℝ) (b R : ℝ) (x : E) : ℝ :=
  radialCutoffLoss R x*f x+radialWallLoss b R x

omit [CompleteSpace E] in
theorem radialWallLoss_contDiff (b : ℝ) {R : ℝ} (hR : 0 < R) (n : ℕ∞) :
    ContDiff ℝ n (radialWallLoss b R : E → ℝ) :=
  radial_norm_contDiff (by positivity : 0 < R/2) (radialWall_contDiff b R)
    (fun r hr => radialWall_zero b hR hr) n

omit [CompleteSpace E] in
theorem radialCutoffLoss_contDiff {R : ℝ} (hR : 0 < R) (n : ℕ∞) :
    ContDiff ℝ n (radialCutoffLoss R : E → ℝ) :=
  radial_norm_contDiff hR
    (fun k => (radialCutoff_contDiff k).comp (contDiff_id.div_const R))
    (fun _ hr => radialCutoff_one ((div_le_one hR).mpr hr)) n

omit [CompleteSpace E] in
theorem radialGlobalization_contDiff {f : E → ℝ} (hf : ContDiff ℝ (3:ℕ) f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) : ContDiff ℝ 3 (radialGlobalization f b R) :=
  ((radialCutoffLoss_contDiff hR 3).mul hf).add (radialWallLoss_contDiff b hR 3)

theorem radialWallLoss_gradient (b : ℝ) {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0) :
    gradient (radialWallLoss b R) x =
      (b*radialRise (‖x‖/R)/‖x‖) • x :=
  (scalar_norm_hasGradientAt hx (radialWall_hasDerivAt b hR ‖x‖)).gradient

theorem radialCutoffLoss_gradient (R : ℝ) {x : E} (hx : x ≠ 0) :
    gradient (radialCutoffLoss R) x =
      (deriv radialCutoff (‖x‖/R)/R/‖x‖) • x := by
  have hd := ((radialCutoff_contDiff 1).differentiable (by norm_num) (‖x‖/R)).hasDerivAt
  simpa only [one_div, div_eq_mul_inv, one_mul, Function.comp_def, id_eq, radialCutoffLoss] using
    (scalar_norm_hasGradientAt hx (hd.comp ‖x‖ ((hasDerivAt_id ‖x‖).div_const R))).gradient

end
end SampleReuse
