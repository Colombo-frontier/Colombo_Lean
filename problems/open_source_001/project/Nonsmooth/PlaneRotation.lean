import Nonsmooth.PerpendicularReflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Module

open MeasureTheory Metric Filter Function
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def circleArc (a b : E) (t : ℝ) : E := Real.cos t • a + Real.sin t • b
def circleTangent (a b : E) (t : ℝ) : E := (-Real.sin t) • a + Real.cos t • b

def planeRotation (a b : E) (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ b)ᗮ.reflection.trans
    (ℝ ∙ (Real.sin (t / 2) • a + (-Real.cos (t / 2)) • b))ᗮ.reflection

theorem orthogonalCombination_norm_sq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ = 0) (s c : ℝ) : ‖s • a + c • b‖ ^ 2 = s ^ 2 + c ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, ha, hb, real_inner_smul_left, real_inner_smul_right, hab, sq_abs]

theorem perpendicularReflection_unit_formula {w : E} (hw : ‖w‖ = 1) (z : E) :
    perpendicularReflection w z = z - (2 * ⟪w, z⟫_ℝ) • w := by
  rw [perpendicularReflection_formula, hw]
  norm_num

theorem circleArc_norm {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ = 0) (t : ℝ) : ‖circleArc a b t‖ = 1 := by
  have h := orthogonalCombination_norm_sq ha hb hab (Real.cos t) (Real.sin t)
  have hs := Real.sin_sq_add_cos_sq t
  change ‖circleArc a b t‖ ^ 2 = _ at h
  nlinarith [norm_nonneg (circleArc a b t)]

theorem circleTangent_norm {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ = 0) (t : ℝ) : ‖circleTangent a b t‖ = 1 := by
  have h := orthogonalCombination_norm_sq ha hb hab (-Real.sin t) (Real.cos t)
  have hs := Real.sin_sq_add_cos_sq t
  change ‖circleTangent a b t‖ ^ 2 = _ at h
  nlinarith [norm_nonneg (circleTangent a b t)]

theorem planeRotation_apply_first {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ = 0) (t : ℝ) : planeRotation a b t a = circleArc a b t := by
  let w := Real.sin (t / 2) • a + (-Real.cos (t / 2)) • b
  have hw : ‖w‖ = 1 := by
    have h := orthogonalCombination_norm_sq ha hb hab (Real.sin (t / 2)) (-Real.cos (t / 2))
    have hs := Real.sin_sq_add_cos_sq (t / 2)
    change ‖w‖ ^ 2 = _ at h
    nlinarith [norm_nonneg w]
  have hba0 : ⟪b, a⟫_ℝ = 0 := (real_inner_comm a b).trans hab
  have hba : perpendicularReflection b a = a := by
    rw [perpendicularReflection_unit_formula hb, hba0]
    simp
  have hwa : ⟪w, a⟫_ℝ = Real.sin (t / 2) := by
    simp [w, inner_add_left, real_inner_smul_left, hba0,
      real_inner_self_eq_norm_sq, ha]
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    have h := Real.sin_two_mul (t / 2)
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul (t / 2)
    have hs := Real.sin_sq_add_cos_sq (t / 2)
    have ht : 2 * (t / 2) = t := by ring
    rw [ht] at h
    linarith
  change perpendicularReflection w (perpendicularReflection b a) = _
  rw [hba, perpendicularReflection_unit_formula hw, hwa]
  dsimp only [w, circleArc]
  rw [hsin, hcos]
  module

theorem planeRotation_apply_second {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ = 0) (t : ℝ) : planeRotation a b t b = circleTangent a b t := by
  let w := Real.sin (t / 2) • a + (-Real.cos (t / 2)) • b
  have hw : ‖w‖ = 1 := by
    have h := orthogonalCombination_norm_sq ha hb hab (Real.sin (t / 2)) (-Real.cos (t / 2))
    have hs := Real.sin_sq_add_cos_sq (t / 2)
    change ‖w‖ ^ 2 = _ at h
    nlinarith [norm_nonneg w]
  have hbb : perpendicularReflection b b = -b := by
    rw [perpendicularReflection_unit_formula hb, real_inner_self_eq_norm_sq, hb]
    norm_num
    module
  have hwb : ⟪w, b⟫_ℝ = -Real.cos (t / 2) := by
    simp [w, inner_add_left, real_inner_smul_left, hab, real_inner_self_eq_norm_sq, hb]
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    have h := Real.sin_two_mul (t / 2)
    have ht : 2 * (t / 2) = t := by ring
    rwa [ht] at h
  have hcos : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (t / 2)
    have ht : 2 * (t / 2) = t := by ring
    rwa [ht] at h
  change perpendicularReflection w (perpendicularReflection b b) = _
  rw [hbb]
  have hn : perpendicularReflection w (-b) = -perpendicularReflection w b :=
    (ℝ ∙ w)ᗮ.reflection.map_neg b
  rw [hn, perpendicularReflection_unit_formula hw, hwb]
  dsimp only [w, circleTangent]
  rw [hsin, hcos]
  module

theorem circleArc_hasDerivAt (a b : E) (t : ℝ) :
    HasDerivAt (circleArc a b) (circleTangent a b t) t :=
  ((Real.hasDerivAt_cos t).smul_const a).add ((Real.hasDerivAt_sin t).smul_const b)

theorem circleArc_zero (a b : E) : circleArc a b 0 = a := by simp [circleArc]

theorem circleArc_pi_div_two (a b : E) : circleArc a b (Real.pi / 2) = b := by simp [circleArc]

end
end Nonsmooth
