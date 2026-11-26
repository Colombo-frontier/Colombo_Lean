import SampleReuse.RandomFrameStopping

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory
open scoped Classical ENNReal

namespace StoppingFullJetPolicy

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def NoStopBefore (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ k < n, π.stop k ω (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () k) = false

/-- Actual extended query count. It is the first stopping index on halting
executions and infinity on nonhalting executions, so no finite-expectation or
almost-sure-termination restriction is imposed. -/
def extendedCost (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, if π.NoStopBefore f n ω then (n : ℝ≥0∞) else 0

theorem extendedCost_eq_cost (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω)
    (hh : π.Halts f ω) : π.extendedCost f ω = (π.cost f ω : ℝ≥0∞) := by
  have hcost : π.cost f ω = Nat.find hh := dif_pos hh
  have hbefore : π.NoStopBefore f (Nat.find hh) ω := by
    intro k hk
    cases h : π.stop k ω (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () k)
    · rfl
    · exact False.elim (Nat.find_min hh hk h)
  rw [hcost]
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : π.NoStopBefore f n ω
    · rw [if_pos hn]
      have hnc : n ≤ Nat.find hh := by
        by_contra h
        have hb := hn (Nat.find hh) (by omega)
        rw [Nat.find_spec hh] at hb
        contradiction
      exact_mod_cast hnc
    · rw [if_neg hn]
      exact zero_le _
  · exact le_iSup_of_le (Nat.find hh) (by rw [if_pos hbefore])

theorem extendedCost_eq_top (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω)
    (hh : ¬π.Halts f ω) : π.extendedCost f ω = ∞ := by
  have hbefore (n : ℕ) : π.NoStopBefore f n ω := by
    intro k hk
    cases h : π.stop k ω (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () k)
    · rfl
    · exact False.elim (hh ⟨k,h⟩)
  simp only [extendedCost, if_pos (hbefore _), ENNReal.iSup_natCast]

theorem fullJet_measurable {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) : Measurable (fullJet f) := by
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  exact hf.continuous.measurable.prodMk
    (hg.continuous.measurable.prodMk (hg.continuous_fderiv (by norm_num)).measurable)

theorem measurable_stop_on_run (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) (n : ℕ) :
    Measurable (fun ω => π.stop n ω
      (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () n)) := by
  have hm := measurable_responseHistory π.query (fun _ (_ : Unit) => fullJet f)
    π.query_measurable (fun _ => (fullJet_measurable hf).comp measurable_snd) n
  exact (π.stop_measurable n).comp
    (measurable_id.prodMk (hm.comp (measurable_id.prodMk measurable_const)))

theorem measurableSet_noStopBefore (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) (n : ℕ) : MeasurableSet {ω | π.NoStopBefore f n ω} := by
  simp only [NoStopBefore, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  exact (π.measurable_stop_on_run hf k) (measurableSet_singleton false)

theorem measurable_extendedCost (π : StoppingFullJetPolicy d Ω) {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : Measurable (π.extendedCost f) :=
  Measurable.iSup (fun n => Measurable.ite (π.measurableSet_noStopBefore hf n)
    measurable_const measurable_const)

/-- Fixed-cap hardness implies an expected-query lower bound even when the
algorithm can fail to halt or has infinite expectation. Success requires an
actual halt with a successful output. -/
theorem extended_expected_calls_from_cap (π : StoppingFullJetPolicy d Ω)
    {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (success : Point d → Prop) (N : ℕ) {p δ : ℝ}
    (hsuccess : p ≤ μ.real {ω | π.Halts f ω ∧ success (π.outputFor f ω)})
    (hcap : μ.real {ω | success ((π.cap N).outputFor f ω)} ≤ δ) :
    ((N+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (p-δ) ≤ ∫⁻ ω, π.extendedCost f ω ∂μ := by
  have hsub : {ω | π.Halts f ω ∧ success (π.outputFor f ω)} ⊆
      {ω | success ((π.cap N).outputFor f ω)} ∪
        {ω | ((N+1 : ℕ) : ℝ≥0∞) ≤ π.extendedCost f ω} := by
    intro ω hω
    obtain ⟨hh,hs⟩ := hω
    by_cases hN : π.cost f ω ≤ N
    · left
      change success ((π.cap N).outputFor f ω)
      rw [π.cap_agrees f ω hh N hN]
      exact hs
    · right
      change ((N+1 : ℕ) : ℝ≥0∞) ≤ π.extendedCost f ω
      rw [π.extendedCost_eq_cost f ω hh]
      exact_mod_cast (show N+1 ≤ π.cost f ω by omega)
  have hprob : p-δ ≤ μ.real {ω | ((N+1 : ℕ) : ℝ≥0∞) ≤ π.extendedCost f ω} := by
    have hm := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
    linarith
  have he := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr hprob
  exact (mul_le_mul_left' he ((N+1 : ℕ) : ℝ≥0∞)).trans
    (mul_meas_ge_le_lintegral (π.measurable_extendedCost hf) ((N+1 : ℕ) : ℝ≥0∞))

end StoppingFullJetPolicy
end SampleReuse.RandomFrame
