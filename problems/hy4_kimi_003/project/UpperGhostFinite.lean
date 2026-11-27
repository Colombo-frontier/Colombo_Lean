import UpperGhostProcess

/-! Actual finite iteration of the coupled Markov kernel and its all-round
failure probability. No divergence probability or conditional sampling contract
is supplied as an assumption. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace Task006.Full

noncomputable def ghostProcessLaw {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E) :
    ℕ → Measure (GhostState E)
  | 0 => Measure.dirac ((x0, x0), false)
  | n + 1 => ghostTransition μ G hG hpos step hstep ∘ₘ ghostProcessLaw μ G hG hpos step hstep x0 n

instance ghostProcessLaw_probability {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    IsProbabilityMeasure (ghostProcessLaw μ G hG hpos step hstep x0 n) := by
  letI := ghostTransition_markov μ G hG hpos step hstep
  induction n with
  | zero => simp only [ghostProcessLaw]; infer_instance
  | succ n ih => rw [ghostProcessLaw]; infer_instance

theorem ghostProcess_failure_le {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E)
    (q : ℝ≥0∞) (hbad : ∀ x, μ (G x)ᶜ ≤ q) (n : ℕ) :
    ghostProcessLaw μ G hG hpos step hstep x0 n ghostFailed ≤ n * q := by
  classical
  let κ := ghostTransition μ G hG hpos step hstep
  letI := ghostTransition_markov μ G hG hpos step hstep
  have hF := measurableSet_ghostFailed (E := E)
  have hcond (j : GhostState E) : κ j ghostFailed ≤ ghostFailed.indicator (fun _ => (1 : ℝ≥0∞)) j + q := by
    change ghostTransition μ G hG hpos step hstep j ghostFailed ≤ _
    rw [ghostTransition_failure]
    by_cases hj : j.2 = true
    · rw [if_pos hj, indicator_of_mem (show j ∈ ghostFailed from hj)]
      exact le_add_right le_rfl
    · rw [if_neg hj, indicator_of_notMem (show j ∉ ghostFailed from hj), zero_add]
      exact hbad j.1.2
  induction n with
  | zero =>
    rw [ghostProcessLaw, Measure.dirac_apply' _ hF]
    simp [ghostFailed]
  | succ n ih =>
    rw [ghostProcessLaw, Measure.bind_apply hF κ.aemeasurable]
    calc
      (∫⁻ j, κ j ghostFailed ∂ghostProcessLaw μ G hG hpos step hstep x0 n) ≤
          ∫⁻ j, ghostFailed.indicator (fun _ => (1 : ℝ≥0∞)) j + q
            ∂ghostProcessLaw μ G hG hpos step hstep x0 n := lintegral_mono hcond
      _ = ghostProcessLaw μ G hG hpos step hstep x0 n ghostFailed + q := by
        rw [lintegral_add_left (measurable_const.indicator hF)]
        simp only [lintegral_indicator_const hF, one_mul, lintegral_const, measure_univ, mul_one]
      _ ≤ (n : ℝ≥0∞) * q + q := add_le_add ih le_rfl
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * q := by simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

theorem ghostProcess_failure_real_le {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E)
    {q : ℝ} (hq : 0 ≤ q) (hbad : ∀ x, μ (G x)ᶜ ≤ ENNReal.ofReal q) (n : ℕ) :
    (ghostProcessLaw μ G hG hpos step hstep x0 n).real ghostFailed ≤ n * q := by
  have h := ghostProcess_failure_le μ G hG hpos step hstep x0 (ENNReal.ofReal q) hbad n
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) h
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hq] using hh

theorem ghostProcess_agreement {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    [MeasurableEq E]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    ∀ᵐ j ∂ghostProcessLaw μ G hG hpos step hstep x0 n, j.2 = false → j.1.1 = j.1.2 := by
  let κ := ghostTransition μ G hG hpos step hstep
  have hEq : MeasurableSet {j : GhostState E | j.2 = false → j.1.1 = j.1.2} := by
    have hflag : MeasurableSet {j : GhostState E | j.2 = false} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have hdiag : MeasurableSet {j : GhostState E | j.1.1 = j.1.2} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    convert hflag.compl.union hdiag using 1
    ext j
    simp only [mem_setOf_eq, mem_union, mem_compl_iff]
    tauto
  induction n with
  | zero => simp [ghostProcessLaw]
  | succ n ih =>
    rw [ghostProcessLaw]
    apply Measure.ae_comp_of_ae_ae hEq
    filter_upwards [ih] with j hj
    rw [ghostTransition_apply]
    exact (ae_map_iff ((ghostUpdate_measurable G hG step hstep).comp measurable_prodMk_left).aemeasurable hEq).mpr
      (ae_of_all _ (fun p => ghostUpdate_agreement G step j p hj))

#print axioms ghostProcess_failure_real_le
#print axioms ghostProcess_agreement
end Task006.Full
