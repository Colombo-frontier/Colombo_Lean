import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FullJet

variable {α : Type} [MeasurableSpace α]

/-- A fixed private probability source for infinitely many independent trials. -/
noncomputable def independentTrialLaw (μ : Measure α) [IsProbabilityMeasure μ] : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => μ)

instance independentTrialLaw_probability (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (independentTrialLaw μ) := by unfold independentTrialLaw; infer_instance

def noSuccessBefore (good : α → Prop) (N : ℕ) : Set (ℕ → α) :=
  {seeds | ∀ i < N, ¬ good (seeds i)}

theorem noSuccessBefore_eq_pi (good : α → Prop) (N : ℕ) :
    noSuccessBefore good N = Set.pi (Finset.range N) (fun _ => {a | ¬ good a}) := by
  ext seeds
  simp only [noSuccessBefore, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]

theorem noSuccessBefore_measurable (good : α → Prop) (hgood : MeasurableSet {a | good a}) (N : ℕ) :
    MeasurableSet (noSuccessBefore good N) := by
  rw [noSuccessBefore_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => hgood.compl)

theorem independentTrialLaw_noSuccess (μ : Measure α) [IsProbabilityMeasure μ]
    (good : α → Prop) (hgood : MeasurableSet {a | good a}) (N : ℕ) :
    independentTrialLaw μ (noSuccessBefore good N) = (μ {a | ¬ good a}) ^ N := by
  rw [independentTrialLaw, noSuccessBefore_eq_pi,
    Measure.infinitePi_pi (μ := fun _ : ℕ => μ) (s := Finset.range N)
      (t := fun _ => {a | ¬ good a}) (fun _ _ => hgood.compl)]
  simp only [Finset.prod_const, Finset.card_range]

theorem independentTrialLaw_noSuccess_real (μ : Measure α) [IsProbabilityMeasure μ]
    (good : α → Prop) (hgood : MeasurableSet {a | good a}) (N : ℕ) :
    (independentTrialLaw μ).real (noSuccessBefore good N) = (μ.real {a | ¬ good a}) ^ N := by
  rw [measureReal_def, independentTrialLaw_noSuccess μ good hgood, ENNReal.toReal_pow]
  rfl

/-- Positive per-trial success implies an actual successful coordinate almost
surely under the infinite product law. -/
theorem independentTrials_success_ae (μ : Measure α) [IsProbabilityMeasure μ]
    (good : α → Prop) (hgood : MeasurableSet {a | good a})
    (hbad : μ.real {a | ¬ good a} ≤ 1 / 4) :
    ∀ᵐ seeds ∂independentTrialLaw μ, ∃ i, good (seeds i) := by
  have hbound (N : ℕ) : (independentTrialLaw μ).real {seeds | ¬ ∃ i, good (seeds i)} ≤
      (1 / 4 : ℝ) ^ N := by
    have hsub : {seeds : ℕ → α | ¬ ∃ i, good (seeds i)} ⊆ noSuccessBefore good N := by
      intro seeds hs i hi hg
      exact hs ⟨i, hg⟩
    apply (measureReal_mono hsub).trans
    rw [independentTrialLaw_noSuccess_real μ good hgood]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hbad N
  have hz : (independentTrialLaw μ).real {seeds | ¬ ∃ i, good (seeds i)} = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    have hlim : Filter.Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact ge_of_tendsto' hlim hbound
  apply ae_iff.mpr
  rcases (ENNReal.toReal_eq_zero_iff _).mp hz with h | h
  · exact h
  · exact False.elim (measure_ne_top (independentTrialLaw μ) _ h)

/-- The sum of survival indicators counts the trials through the first
success, and is infinite on the exceptional never-successful streams. -/
noncomputable def trialEnvelope (good : α → Prop) (seeds : ℕ → α) : ℝ≥0∞ :=
  ∑' N : ℕ, (noSuccessBefore good N).indicator (fun _ => (1 : ℝ≥0∞)) seeds

theorem trialEnvelope_measurable (good : α → Prop) (hgood : MeasurableSet {a | good a}) :
    Measurable (trialEnvelope good) := by
  apply Measurable.ennreal_tsum
  intro N
  exact measurable_const.indicator (noSuccessBefore_measurable good hgood N)

theorem lintegral_trialEnvelope (μ : Measure α) [IsProbabilityMeasure μ]
    (good : α → Prop) (hgood : MeasurableSet {a | good a}) :
    ∫⁻ seeds, trialEnvelope good seeds ∂independentTrialLaw μ =
      ∑' N : ℕ, (μ {a | ¬ good a}) ^ N := by
  unfold trialEnvelope
  rw [lintegral_tsum (fun N => (measurable_const.indicator
    (noSuccessBefore_measurable good hgood N)).aemeasurable)]
  apply tsum_congr
  intro N
  rw [lintegral_indicator_const (noSuccessBefore_measurable good hgood N), one_mul,
    independentTrialLaw_noSuccess μ good hgood N]

/-- A quarter failure probability bounds the expected number of trials by
4/3. This integral belongs to the fixed, actual infinite product source. -/
theorem lintegral_trialEnvelope_le (μ : Measure α) [IsProbabilityMeasure μ]
    (good : α → Prop) (hgood : MeasurableSet {a | good a})
    (hbad : μ.real {a | ¬ good a} ≤ 1 / 4) :
    ∫⁻ seeds, trialEnvelope good seeds ∂independentTrialLaw μ ≤ (4 / 3 : ℝ≥0∞) := by
  have hbad' : μ {a | ¬ good a} ≤ (1 / 4 : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).mp
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hbad
  rw [lintegral_trialEnvelope μ good hgood]
  calc
    _ ≤ ∑' N : ℕ, (1 / 4 : ℝ≥0∞) ^ N := ENNReal.tsum_le_tsum (fun N => pow_le_pow_left' hbad' N)
    _ = 4 / 3 := by
      rw [ENNReal.tsum_geometric]
      have h4 : (4 : ℝ≥0∞) / 4 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
      have hs : (1 : ℝ≥0∞) - 1 / 4 = 3 / 4 := by
        calc
          _ = 4 / 4 - 1 / 4 := by rw [h4]
          _ = (4 - 1) / 4 := (ENNReal.sub_div (fun _ _ => by norm_num)).symm
          _ = 3 / 4 := by
            have hsub := ENNReal.natCast_sub 4 1
            norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hsub
            rw [← hsub]
      rw [hs, ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]

end FullJet
