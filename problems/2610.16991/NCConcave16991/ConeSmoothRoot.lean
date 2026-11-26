import NCConcave16991.ConeRecoveryDifferential
import NCConcave16991.ConeSmoothFunctions

/-! # Uniform first and second bounds for regularized Euclidean norms -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConeRecovery Set
open scoped InnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rootNorm (a : ℝ) (x : E) : ℝ := Real.sqrt (a + ‖x‖ ^ 2)
def rootGradient (a : ℝ) (x : E) : E := (rootNorm a x)⁻¹ • x

theorem rootNorm_pos {a : ℝ} (ha : 0 < a) (x : E) : 0 < rootNorm a x := by
  unfold rootNorm
  positivity

theorem norm_le_rootNorm {a : ℝ} (ha : 0 < a) (x : E) : ‖x‖ ≤ rootNorm a x := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ a + ‖x‖ ^ 2)
  change ‖x‖ ≤ Real.sqrt (a + ‖x‖ ^ 2)
  nlinarith [Real.sqrt_nonneg (a + ‖x‖ ^ 2), norm_nonneg x]

theorem sqrt_le_rootNorm {a : ℝ} (ha : 0 < a) (x : E) : Real.sqrt a ≤ rootNorm a x :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])

theorem rootNorm_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (rootNorm a : E → ℝ) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x ↦ by positivity)

theorem rootNorm_fderiv {a : ℝ} (ha : 0 < a) (x : E) :
    fderiv ℝ (rootNorm a : E → ℝ) x = innerSL ℝ (rootGradient a x) := by
  change fderiv ℝ (fun z : E ↦ Real.sqrt (a + ‖z‖ ^ 2)) x = _
  rw [(sqrt_norm_sq_hasFDerivAt ha x).fderiv]
  exact ((innerSL ℝ).map_smul ((rootNorm a x)⁻¹) x).symm

theorem rootNorm_fderiv_norm_le {a : ℝ} (ha : 0 < a) (x : E) :
    ‖fderiv ℝ (rootNorm a : E → ℝ) x‖ ≤ 1 := by
  rw [rootNorm_fderiv ha, innerSL_apply_norm, rootGradient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (rootNorm_pos ha x))]
  have hh := mul_le_mul_of_nonneg_left (norm_le_rootNorm ha x)
    (inv_nonneg.mpr (rootNorm_pos ha x).le)
  simpa only [inv_mul_cancel₀ (rootNorm_pos ha x).ne'] using hh

theorem rootNorm_sub_bound {a : ℝ} (ha : 0 < a) (x y : E) :
    |rootNorm a x - rootNorm a y| ≤ ‖x - y‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := rootNorm a) (fun z _ ↦ (rootNorm_contDiff ha).differentiable (by simp) z)
    (fun z _ ↦ rootNorm_fderiv_norm_le ha z) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using hh

theorem rootGradient_sub_bound {a : ℝ} (ha : 0 < a) (x y : E) :
    ‖rootGradient a x - rootGradient a y‖ ≤ (2 / Real.sqrt a) * ‖x - y‖ := by
  have hs := rootNorm_pos ha x
  have ht := rootNorm_pos ha y
  have hroot := Real.sqrt_pos.mpr ha
  have he : rootGradient a x - rootGradient a y =
      (rootNorm a x)⁻¹ • (x - y) + ((rootNorm a x)⁻¹ - (rootNorm a y)⁻¹) • y := by
    simp only [rootGradient, smul_sub, sub_smul]
    abel
  have hcoeff : |(rootNorm a x)⁻¹ - (rootNorm a y)⁻¹| =
      |rootNorm a y - rootNorm a x| / (rootNorm a x * rootNorm a y) := by
    rw [inv_sub_inv hs.ne' ht.ne', abs_div, abs_mul, abs_of_pos hs, abs_of_pos ht]
  have hc : |(rootNorm a x)⁻¹ - (rootNorm a y)⁻¹| * ‖y‖ ≤
      |rootNorm a y - rootNorm a x| / rootNorm a x := by
    rw [hcoeff]
    have hh := mul_le_mul_of_nonneg_left (norm_le_rootNorm ha y)
      (div_nonneg (abs_nonneg (rootNorm a y - rootNorm a x)) (mul_pos hs ht).le)
    exact hh.trans_eq (by field_simp)
  have htri := norm_add_le ((rootNorm a x)⁻¹ • (x - y))
    (((rootNorm a x)⁻¹ - (rootNorm a y)⁻¹) • y)
  rw [he]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at htri
  have hlip := rootNorm_sub_bound ha y x
  rw [norm_sub_rev y x] at hlip
  have hfrac := div_le_div_of_nonneg_right hlip hs.le
  have hrec := one_div_le_one_div_of_le hroot (sqrt_le_rootNorm ha x)
  have hmul := mul_le_mul_of_nonneg_right hrec (norm_nonneg (x - y))
  simp only [div_eq_mul_inv, one_mul] at hc hfrac hmul ⊢
  nlinarith

theorem rootNorm_fderiv_sub_bound {a : ℝ} (ha : 0 < a) (x y : E) :
    ‖fderiv ℝ (rootNorm a : E → ℝ) x - fderiv ℝ (rootNorm a : E → ℝ) y‖ ≤
      (2 / Real.sqrt a) * ‖x - y‖ := by
  rw [rootNorm_fderiv ha, rootNorm_fderiv ha, ← map_sub, innerSL_apply_norm]
  exact rootGradient_sub_bound ha x y

end NCConcave16991.ConeSmooth
