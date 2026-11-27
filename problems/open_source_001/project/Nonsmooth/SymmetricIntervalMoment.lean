import Nonsmooth.StrongPotentialHalfline
import Nonsmooth.TruncationMonotonicity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem central_interval_second_unnormalized (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun x : ℝ => x ^ 2) ν) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in Icc (-r) r, x ^ 2 ∂ν) ≤ ν.real (Icc (-r) r) * ∫ x : ℝ, x ^ 2 ∂ν := by
  by_cases hpos : ν (Icc (-r) r) = 0
  · simp [hpos, measureReal_def]
  · have he := integral_event_le_of_separated hi measurableSet_Icc hpos (r ^ 2)
      (by
        filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Icc] with x hx
        change -r ≤ x ∧ x ≤ r at hx
        nlinarith)
      (by
        filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Icc.compl] with x hx
        have hn : ¬ (-r ≤ x ∧ x ≤ r) := hx
        rcases not_and_or.mp hn with h | h <;> nlinarith)
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] at he
    have hp : 0 < ν.real (Icc (-r) r) := ENNReal.toReal_pos hpos (measure_ne_top _ _)
    change (ν.real (Icc (-r) r))⁻¹ * (∫ x in Icc (-r) r, x ^ 2 ∂ν) ≤ _ at he
    rw [← div_eq_inv_mul, div_le_iff₀ hp] at he
    simpa only [mul_comm] using he

theorem symmetric_straddling_interval_integral (ν : Measure ℝ)
    (hneg : ν.map (fun x : ℝ => -x) = ν) {f : ℝ → ℝ} (hi : Integrable f ν)
    (hf : ∀ x : ℝ, f (-x) = f x) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    2 * (∫ x in Icc a b, f x ∂ν) =
      (∫ x in Icc a (-a), f x ∂ν) + ∫ x in Icc (-b) b, f x ∂ν := by
  let e : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hp : MeasurePreserving e ν ν := ⟨e.continuous.measurable, hneg⟩
  have hcomp : Integrable (fun x : ℝ => (Icc a b).indicator f (-x)) ν :=
    (hp.integrable_comp_emb e.toMeasurableEquiv.measurableEmbedding).mpr (hi.indicator measurableSet_Icc)
  have he := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding ((Icc a b).indicator f)
  change (∫ x : ℝ, (Icc a b).indicator f (-x) ∂ν) = ∫ x : ℝ, (Icc a b).indicator f x ∂ν at he
  have hpoint (x : ℝ) : (Icc a b).indicator f x + (Icc a b).indicator f (-x) =
      (Icc a (-a)).indicator f x + (Icc (-b) b).indicator f x := by
    have hca : x ≤ -a ↔ a ≤ -x := by constructor <;> intro h <;> linarith
    have hdb : -b ≤ x ↔ -x ≤ b := by constructor <;> intro h <;> linarith
    simp only [Set.indicator, mem_Icc, hca, hdb, hf]
    by_cases h1 : a ≤ x <;> by_cases h2 : x ≤ b <;>
      by_cases h3 : a ≤ -x <;> by_cases h4 : -x ≤ b <;> simp [h1, h2, h3, h4] <;> linarith
  have h := integral_congr_ae (μ := ν) (Eventually.of_forall hpoint)
  rw [integral_add (hi.indicator measurableSet_Icc) hcomp,
    integral_add (hi.indicator measurableSet_Icc) (hi.indicator measurableSet_Icc), he,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
    integral_indicator measurableSet_Icc] at h
  linarith

/-- For any symmetric law, conditioning on an interval containing zero cannot
increase its second moment, even when the interval is asymmetric. -/
theorem symmetric_straddling_interval_second (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν.map (fun x : ℝ => -x) = ν) (hi : Integrable (fun x : ℝ => x ^ 2) ν)
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    (∫ x : ℝ, x ^ 2 ∂ν[|Icc a b]) ≤ ∫ x : ℝ, x ^ 2 ∂ν := by
  by_cases hz : ν (Icc a b) = 0
  · rw [cond_eq_zero_of_meas_eq_zero hz, integral_zero_measure]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hp : 0 < ν.real (Icc a b) := ENNReal.toReal_pos hz (measure_ne_top _ _)
  have hmass := symmetric_straddling_interval_integral ν hneg (integrable_const (1 : ℝ))
    (fun _ => rfl) ha hb
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ] at hmass
  change 2 * ν.real (Icc a b) = ν.real (Icc a (-a)) + ν.real (Icc (-b) b) at hmass
  have hleft : (∫ x in Icc a (-a), x ^ 2 ∂ν) ≤ ν.real (Icc a (-a)) * ∫ x : ℝ, x ^ 2 ∂ν := by
    simpa only [neg_neg] using central_interval_second_unnormalized ν hi (neg_nonneg.mpr ha)
  have hright := central_interval_second_unnormalized ν hi hb
  have hsum := add_le_add hleft hright
  rw [← add_mul, ← hmass] at hsum
  have he := symmetric_straddling_interval_integral ν hneg hi (fun x => by ring) ha hb
  rw [← he] at hsum
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change (ν.real (Icc a b))⁻¹ * (∫ x in Icc a b, x ^ 2 ∂ν) ≤ _
  rw [← div_eq_inv_mul, div_le_iff₀ hp]
  nlinarith

end
end Nonsmooth
