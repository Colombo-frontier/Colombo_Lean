import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Relative-entropy transfer for a rare event

The variational lemma is adapted from the local, kernel-checked proof in
`Lean1/FreshGradientMinimax0111/FreshGradientMinimax/EntropyTesting.lean`.

The new event inequality uses a fixed negative exponential tilt instead of
Pinsker. For the manuscript's rare bad event it is sufficient, and gives
`P(B) ≤ (4/3) (KL(Q || P) + log(4) Q(B))`. All measures, integrals and KL
divergences below are the actual mathlib objects. No transfer conclusion is
assumed as a hypothesis.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace MatchingBounds1005.EventTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem entropy_variational_lower {f : Ω → ℝ} (hQP : Q ≪ P)
    (hi : Integrable (llr Q P) Q) (hf : Integrable f Q)
    (he : Integrable (fun x => Real.exp (f x)) P) :
    (∫ x, f x ∂Q) - Real.log (∫ x, Real.exp (f x) ∂P) ≤ ∫ x, llr Q P x ∂Q := by
  letI : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted he
  have hc : Q ≪ P.tilted f := hQP.trans (absolutelyContinuous_tilted he)
  have h := integral_llr_add_sub_measure_univ_nonneg hc
    (integrable_llr_tilted_right hQP hf hi he)
  rw [integral_llr_tilted_right hQP hf he hi] at h
  simp only [measureReal_univ_eq_one, add_sub_cancel_right] at h
  linarith

def eventPenalty (B : Set Ω) : Ω → ℝ := B.indicator (fun _ => -Real.log 4)

omit [MeasurableSpace Ω] in
theorem eventPenalty_exp (B : Set Ω) (x : Ω) :
    Real.exp (eventPenalty B x) = 1 + B.indicator (fun _ => (-3 / 4 : ℝ)) x := by
  by_cases hx : x ∈ B
  · norm_num [eventPenalty, hx, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  · simp [eventPenalty, hx]

/-- A rare-event transfer in the direction needed by the manuscript:
the divergence is `KL(Q || P)`, whereas the conclusion bounds `P(B)`. -/
theorem probability_event_le_kl (B : Set Ω) (hB : MeasurableSet B)
    (hKL : klDiv Q P ≠ ∞) :
    P.real B ≤ (4 / 3 : ℝ) * ((klDiv Q P).toReal + Real.log 4 * Q.real B) := by
  obtain ⟨hQP, hi⟩ := klDiv_ne_top_iff.mp hKL
  have hf : Integrable (eventPenalty B) Q := (integrable_const _).indicator hB
  have he : Integrable (fun x => Real.exp (eventPenalty B x)) P := by
    simp_rw [eventPenalty_exp]
    exact (integrable_const 1).add ((integrable_const (-3 / 4 : ℝ)).indicator hB)
  have hfi : (∫ x, eventPenalty B x ∂Q) = -Real.log 4 * Q.real B := by
    simp [eventPenalty, integral_indicator hB, smul_eq_mul, mul_comm]
  have hei : (∫ x, Real.exp (eventPenalty B x) ∂P) = 1 - (3 / 4 : ℝ) * P.real B := by
    simp_rw [eventPenalty_exp]
    rw [integral_add (integrable_const 1) ((integrable_const (-3 / 4 : ℝ)).indicator hB)]
    simp [integral_indicator hB, smul_eq_mul]
    ring
  have ht := entropy_variational_lower hQP hi hf he
  rw [hfi, hei] at ht
  have hprob : P.real B ≤ 1 := measureReal_le_one
  have hpos : 0 < 1 - (3 / 4 : ℝ) * P.real B := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hkl : (klDiv Q P).toReal = ∫ x, llr Q P x ∂Q := by
    simpa using toReal_klDiv hQP hi
  rw [← hkl] at ht
  linarith

/-- Quantitative form when the reference event probability and actual KL
have already been bounded. -/
theorem probability_event_le_of_bounds (B : Set Ω) (hB : MeasurableSet B)
    (hKL : klDiv Q P ≠ ∞) {κ ζ : ℝ}
    (hκ : (klDiv Q P).toReal ≤ κ) (hζ : Q.real B ≤ ζ) :
    P.real B ≤ (4 / 3 : ℝ) * (κ + Real.log 4 * ζ) := by
  have h := probability_event_le_kl B hB hKL
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hζ hlog
  linarith

/-- The final conditioning step, expressed as the exact conditional-event
ratio. `hsub` is the pointwise first-exit/certificate implication. The coupling
and certificate establishing that implication must be supplied separately. -/
theorem conditioned_event_ratio_le (B success good : Set Ω) (hB : MeasurableSet B)
    (hKL : klDiv Q P ≠ ∞) {κ ζ g : ℝ}
    (hκ : (klDiv Q P).toReal ≤ κ) (hζ : Q.real B ≤ ζ)
    (hsub : success ∩ good ⊆ B) (hg : 0 < g) (hgood : g ≤ P.real good) :
    P.real (success ∩ good) / P.real good ≤
      ((4 / 3 : ℝ) * (κ + Real.log 4 * ζ)) / g := by
  have hb := probability_event_le_of_bounds B hB hKL hκ hζ
  have hs : P.real (success ∩ good) ≤ P.real B := measureReal_mono hsub
  have hb0 : 0 ≤ (4 / 3 : ℝ) * (κ + Real.log 4 * ζ) :=
    ENNReal.toReal_nonneg.trans hb
  calc
    _ ≤ ((4 / 3 : ℝ) * (κ + Real.log 4 * ζ)) / P.real good :=
      div_le_div_of_nonneg_right (hs.trans hb) (hg.le.trans hgood)
    _ ≤ _ := div_le_div_of_nonneg_left hb0 hg hgood

end MatchingBounds1005.EventTransfer
