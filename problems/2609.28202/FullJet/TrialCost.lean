import FullJet.InfiniteTrials
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped ENNReal BigOperators

namespace FullJet

variable {α : Type} [MeasurableSpace α]

theorem trialEnvelope_ge_of_failures (good : α → Prop) (seeds : ℕ → α) (K : ℕ)
    (hfail : ∀ i < K, ¬ good (seeds i)) :
    (K + 1 : ℝ≥0∞) ≤ trialEnvelope good seeds := by
  classical
  have hmem (j : ℕ) (hj : j ∈ Finset.range (K + 1)) : seeds ∈ noSuccessBefore good j := by
    intro i hi
    exact hfail i (by simp only [Finset.mem_range] at hj; omega)
  have hsum : ∑ j ∈ Finset.range (K + 1),
      (noSuccessBefore good j).indicator (fun _ => (1 : ℝ≥0∞)) seeds = K + 1 := by
    rw [Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem (hmem j hj) _)]
    simp
  rw [← hsum]
  exact ENNReal.sum_le_tsum _

/-- A measurable nonnegative cost dominated by N times the survival sum
is integrable, with expected cost at most 4N/3. -/
theorem trialCost_integrable_bound (μ : Measure α) [IsProbabilityMeasure μ]
    (good : α → Prop) (hgood : MeasurableSet {a | good a})
    (hbad : μ.real {a | ¬ good a} ≤ 1 / 4)
    (cost : (ℕ → α) → ℝ) (hmeas : Measurable cost) (hnonneg : ∀ s, 0 ≤ cost s)
    (N : ℕ) (hcost : ∀ᵐ s ∂independentTrialLaw μ,
      ENNReal.ofReal (cost s) ≤ (N : ℝ≥0∞) * trialEnvelope good s) :
    Integrable cost (independentTrialLaw μ) ∧ ∫ s, cost s ∂independentTrialLaw μ ≤ (N : ℝ) * (4 / 3) := by
  have hb : ∫⁻ s, ENNReal.ofReal (cost s) ∂independentTrialLaw μ ≤ (N : ℝ≥0∞) * (4 / 3) := by
    calc
      _ ≤ ∫⁻ s, (N : ℝ≥0∞) * trialEnvelope good s ∂independentTrialLaw μ := lintegral_mono_ae hcost
      _ = (N : ℝ≥0∞) * ∫⁻ s, trialEnvelope good s ∂independentTrialLaw μ :=
        lintegral_const_mul _ (trialEnvelope_measurable good hgood)
      _ ≤ _ := mul_le_mul_left' (lintegral_trialEnvelope_le μ good hgood hbad) _
  have hfinite : (N : ℝ≥0∞) * (4 / 3) < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) (ENNReal.div_lt_top (by norm_num) (by norm_num))
  have hi : Integrable cost (independentTrialLaw μ) :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mpr
      (hb.trans_lt hfinite)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg) hmeas.aestronglyMeasurable]
  have hreal := ENNReal.toReal_mono hfinite.ne hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] using hreal

end FullJet
