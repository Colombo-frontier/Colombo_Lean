import Nonsmooth.FiniteSupport

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem linear_unitBall_minimum (a : E) : minimumValue 1 (fun x : E => ⟪a, x⟫_ℝ) = -‖a‖ := by
  by_cases ha : a = 0
  · subst a
    simpa using (minimumValue_eq (f := fun x : E => ⟪(0 : E), x⟫_ℝ)
      (x := 0) (by simp) (fun y _ => by simp))
  have hn := normalizedDirection_norm ha
  have hv : ⟪a, -normalizedDirection a⟫_ℝ = -‖a‖ := by
    simp only [inner_neg_right, normalizedDirection, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hm : minimumValue 1 (fun x : E => ⟪a, x⟫_ℝ) = ⟪a, -normalizedDirection a⟫_ℝ := by
    apply minimumValue_eq (by simp only [norm_neg, hn, le_refl])
    intro y hy
    rw [hv]
    have h := real_inner_le_norm a (-y)
    rw [inner_neg_right, norm_neg] at h
    have hmul := mul_le_mul_of_nonneg_left hy (norm_nonneg a)
    linarith
  exact hm.trans hv

theorem boundedFiniteSupport_single (a : BoundedSupportRows E (Fin 1)) (x : E) :
    boundedFiniteSupport a x = ⟪(a 0).val, x⟫_ℝ := by
  obtain ⟨i, hi⟩ := finiteSupport_attained (fun i => (a i).val) x
  change finiteSupport (fun i => (a i).val) x = _
  simpa only [Fin.eq_zero i] using hi

theorem boundedFiniteSupport_single_minimum (a : BoundedSupportRows E (Fin 1)) :
    minimumValue 1 (boundedFiniteSupport a) = -‖(a 0).val‖ := by
  have he : boundedFiniteSupport a = (fun x => ⟪(a 0).val, x⟫_ℝ) := funext (boundedFiniteSupport_single a)
  rw [he, linear_unitBall_minimum]

end
end Nonsmooth
