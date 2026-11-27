import Nonsmooth.GaussianWinnerCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem symmetric_halfspace_integral (ν : Measure ℝ)
    (hneg : ν.map (fun x : ℝ => -x) = ν) {f : ℝ → ℝ} (hi : Integrable f ν)
    (hf : ∀ x : ℝ, f (-x) = f x) {b : ℝ} (hb : 0 ≤ b) :
    2 * (∫ x in Iic b, f x ∂ν) = (∫ x, f x ∂ν) + ∫ x in Icc (-b) b, f x ∂ν := by
  let e : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hp : MeasurePreserving e ν ν := ⟨e.continuous.measurable, hneg⟩
  have hcomp : Integrable (fun x : ℝ => (Iic b).indicator f (-x)) ν :=
    (hp.integrable_comp_emb e.toMeasurableEquiv.measurableEmbedding).mpr (hi.indicator measurableSet_Iic)
  have he := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding ((Iic b).indicator f)
  change (∫ x : ℝ, (Iic b).indicator f (-x) ∂ν) = ∫ x : ℝ, (Iic b).indicator f x ∂ν at he
  have hpoint (x : ℝ) : (Iic b).indicator f x + (Iic b).indicator f (-x) =
      f x + (Icc (-b) b).indicator f x := by
    by_cases hx : x ≤ b <;> by_cases hnx : -x ≤ b
    · have hi : x ∈ Icc (-b) b := ⟨by linarith, hx⟩
      simp [hx, hnx, hi, hf]
    · have hi : x ∉ Icc (-b) b := by intro h; linarith [h.1]
      simp [hx, hnx, hi]
    · have hi : x ∉ Icc (-b) b := fun h => hx h.2
      simp [hx, hnx, hi, hf]
    · exfalso
      linarith
  have h := integral_congr_ae (μ := ν) (Eventually.of_forall hpoint)
  rw [integral_add (hi.indicator measurableSet_Iic) hcomp,
    integral_add hi (hi.indicator measurableSet_Icc), he,
    integral_indicator measurableSet_Iic, integral_indicator measurableSet_Icc] at h
  linarith

theorem symmetric_nonnegative_halfspace_second (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν.map (fun x : ℝ => -x) = ν) (hi : Integrable (fun x : ℝ => x ^ 2) ν)
    {b : ℝ} (hb : 0 ≤ b) :
    (∫ x : ℝ, x ^ 2 ∂ν[|Iic b]) ≤ ∫ x : ℝ, x ^ 2 ∂ν := by
  have hmass := symmetric_halfspace_integral ν hneg (integrable_const (1 : ℝ))
    (fun _ => rfl) hb
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply_univ, measure_univ, ENNReal.toReal_one] at hmass
  change 2 * ν.real (Iic b) = 1 + ν.real (Icc (-b) b) at hmass
  have hpa : 0 < ν.real (Iic b) := by linarith [measureReal_nonneg (μ := ν) (s := Icc (-b) b)]
  have hsmall : (∫ x in Icc (-b) b, x ^ 2 ∂ν) ≤
      ν.real (Icc (-b) b) * (∫ x : ℝ, x ^ 2 ∂ν) := by
    by_cases hpos : ν (Icc (-b) b) = 0
    · simp [hpos, measureReal_def]
    · have he := integral_event_le_of_separated hi measurableSet_Icc hpos (b ^ 2)
        (by
          filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Icc] with x hx
          change -b ≤ x ∧ x ≤ b at hx
          nlinarith)
        (by
          filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Icc.compl] with x hx
          have hn : ¬ (-b ≤ x ∧ x ≤ b) := hx
          rcases not_and_or.mp hn with h | h <;> nlinarith)
      rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] at he
      have hp : 0 < ν.real (Icc (-b) b) := ENNReal.toReal_pos hpos (measure_ne_top _ _)
      change (ν.real (Icc (-b) b))⁻¹ * (∫ x in Icc (-b) b, x ^ 2 ∂ν) ≤ _ at he
      rw [← div_eq_inv_mul, div_le_iff₀ hp] at he
      simpa only [mul_comm] using he
  have hs := symmetric_halfspace_integral ν hneg hi (fun x => by ring) hb
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change (ν.real (Iic b))⁻¹ * (∫ x in Iic b, x ^ 2 ∂ν) ≤ _
  rw [← div_eq_inv_mul, div_le_iff₀ hpa]
  have hmass' : ν.real (Icc (-b) b) = 2 * ν.real (Iic b) - 1 := by linarith
  rw [hmass'] at hsmall
  nlinarith

end
end Nonsmooth
