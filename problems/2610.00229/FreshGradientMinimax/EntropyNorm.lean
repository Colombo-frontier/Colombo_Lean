import FreshGradientMinimax.EntropyTesting

/-! Finite KL controls the absolute first moment of the log likelihood.
This supplies uniform integrability for adaptive composition without any
bound on the query locations. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory InformationTheory
open scoped ENNReal

theorem mul_abs_log_le (r : ℝ) (hr : 0 ≤ r) :
    r * |Real.log r| ≤ r * Real.log r + 2 := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · simp [← hr0]
  have h := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log hr) hr
  rw [mul_neg, mul_inv_cancel₀ hr0.ne'] at h
  rcases le_or_lt 0 (Real.log r) with hl | hl
  · rw [abs_of_nonneg hl]; linarith
  · rw [abs_of_neg hl]; nlinarith

theorem llr_integral_norm_le {α : Type*} [MeasurableSpace α]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P) :
    (∫ x, ‖llr P Q x‖ ∂P) ≤ (∫ x, llr P Q x ∂P) + 2 := by
  have hiw := (integrable_rnDeriv_smul_iff hPQ).mpr hi
  have hnw := (integrable_rnDeriv_smul_iff hPQ).mpr hi.norm
  have h := integral_mono hnw (hiw.add (integrable_const 2)) (fun x => by
    simpa only [smul_eq_mul, llr, Real.norm_eq_abs] using
      mul_abs_log_le (P.rnDeriv Q x).toReal ENNReal.toReal_nonneg)
  dsimp only [Pi.add_apply] at h
  rw [integral_add hiw (integrable_const 2), integral_rnDeriv_smul hPQ,
    integral_rnDeriv_smul hPQ] at h
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem finite_kl_information_bound {α : Type*} [MeasurableSpace α]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : ℝ} (hc : 0 ≤ c) (h : klDiv P Q ≤ ENNReal.ofReal c) :
    P ≪ Q ∧ Integrable (llr P Q) P ∧ (∫ x, llr P Q x ∂P) ≤ c ∧
      (∫ x, ‖llr P Q x‖ ∂P) ≤ c + 2 := by
  have ht : klDiv P Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  obtain ⟨ha, hi⟩ := klDiv_ne_top_iff.mp ht
  have hb : (∫ x, llr P Q x ∂P) ≤ c := by
    rw [klDiv_of_ac_of_integrable ha hi] at h
    simp only [measureReal_univ_eq_one, add_sub_cancel_right] at h
    exact (ENNReal.ofReal_le_ofReal_iff hc).mp h
  exact ⟨ha, hi, hb, (llr_integral_norm_le ha hi).trans (add_le_add_right hb 2)⟩

end FreshGradientMinimax

