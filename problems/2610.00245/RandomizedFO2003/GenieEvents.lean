import RandomizedFO2003.SpectralCensoredBarrier
import RandomizedFO2003.CascadePrefixInduction
import RandomizedFO2003.OperatorRunMeasurability
import RandomizedFO2003.TerminalEvent

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Primitives
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))
  {Seed : Type} [MeasurableSpace Seed]

noncomputable def publicCascadeCoefficients (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (i : Fin (N + 1)) (p : Sample K N) : Coefficients N (BlockSpace K) :=
  decoderCoefficients (S.cascadeCoefficients K N h p) i 0

theorem publicCascadeCoefficients_eq (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (i : Fin (N + 1)) (p : Sample K N) :
    S.publicCascadeCoefficients K N h i p =
      ((S.cascade K N (fun j => isometry _ (p.2 j)) p.1 h).publicData i).coefficients := rfl

theorem measurable_publicCascadeCoefficients (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) (i : Fin (N + 1)) :
    Measurable (S.publicCascadeCoefficients K N h i) := by
  letI : BorelSpace (Coefficients N (BlockSpace K)) := Prod.borelSpace
  exact (continuous_decoderCoefficients (E := BlockSpace K) i).measurable.comp
    ((S.measurable_cascadeCoefficients K N h).prodMk measurable_const)

theorem measurable_censoredGenieHistory (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    Measurable (fun p : Sample K N × Seed => S.censoredGenieHistory K N h A T i p.1.1 p.1.2 p.2) := by
  have hU : Measurable (fun p : Sample K N × Seed => (p.1.2 i : BlockSpace K →L[ℝ] BlockSpace K)) :=
    measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst.snd)
  have hh : Measurable (fun p : Sample K N × Seed =>
      (p.1.1 i, S.publicCascadeCoefficients K N h i p.1, p.2)) :=
    ((measurable_pi_apply i).comp measurable_fst.fst).prodMk
      (((S.measurable_publicCascadeCoefficients K N h i).comp measurable_fst).prodMk measurable_snd)
  exact ((S.censoredGenieProgram K N h A T i).compile (continuousDiagonal K S.node) (T + 1) Prod.fst
    measurable_fst).run_family_measurable (markedActionCount (T + 1)) _ hU _ hh

/-- All block events live on the same original sample and private-seed
space. Their independence is not assumed or needed for the union bound. -/
def censoredGenieGoodEvent (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) : Set (Sample K N × Seed) :=
  {p | S.censoredGenieHistory K N h A T i p.1.1 p.1.2 p.2 ∈
    historyWeightEvent K S.weight (T + 1) Prod.fst (1 / 32) ∩
      (S.censoredGenieProgram K N h A T i).prefixFlatEvent K S.residual m (T + 1) Prod.fst
        (radiusCoefficient * h / γ) (h / (64 * γ))}

theorem measurableSet_censoredGenieGoodEvent (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    MeasurableSet (S.censoredGenieGoodEvent K N h A T i) := by
  exact ((measurableSet_historyWeightEvent K S.weight (T + 1) Prod.fst measurable_fst (1 / 32)).inter
    ((S.censoredGenieProgram K N h A T i).measurableSet_prefixFlatEvent K S.residual m (T + 1) Prod.fst
      measurable_fst (radiusCoefficient * h / γ) (h / (64 * γ)))).preimage
        (S.measurable_censoredGenieHistory K N h A T i)

theorem censoredGenieGoodEvent_weights (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    {p : Sample K N × Seed} (hp : p ∈ S.censoredGenieGoodEvent K N h A T i) :
    ∀ j, |SpectralCoordinates.weight K (p.1.1 i) j - S.weight j| ≤ (1 / 32) * S.weight j := by
  have hs : ActionHistory.seed (BlockSpace K) (markedActionCount (T + 1))
      (S.censoredGenieHistory K N h A T i p.1.1 p.1.2 p.2) =
      (p.1.1 i, S.publicCascadeCoefficients K N h i p.1, p.2) := ActionProgram.run_seed _ _ _ _
  intro j
  have hj := hp.1 j
  rw [hs] at hj
  exact hj

theorem cascadeGoodEvent_of_genie_events (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ)
    {p : Sample K N × Seed} (hunit : ∀ i, ‖p.1.1 i‖ = 1)
    (hp : ∀ i, p ∈ S.censoredGenieGoodEvent K N h A T i) : p.1.1 ∈ S.cascadeGoodEvent K N :=
  fun i => ⟨hunit i, S.censoredGenieGoodEvent_weights K N h A T i (hp i)⟩

/-- On the intersection of all concrete genie events, the final gate of
the actual sampled function is flat at the original algorithm's output. -/
theorem terminalFlat_of_genie_events (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (hT : T < (N + 1) * m)
    {p : Sample K N × Seed} (hp : ∀ i, p ∈ S.censoredGenieGoodEvent K N h A T i) :
    p ∈ S.terminalFlatEvent K N h A T (Fin.last N) := by
  have hb := fun i => S.censoredPrefixBarrier_of_genie K N h A T i p.1.1 p.1.2 p.2 (hp i).2
  exact (S.cascade K N (fun i => isometry _ (p.1.2 i)) p.1.1 h).terminal_flat_of_censored_barriers
    (cascadeCoordinates K N) A p.2 T m hb hT

theorem terminal_bad_probability_le_genie_bad (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (ν : Measure Seed) (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed)
    (T : ℕ) (hT : T < (N + 1) * m) :
    ((S.cascadeParameterLaw K N).prod ν) (S.terminalFlatEvent K N h A T (Fin.last N))ᶜ ≤
      ∑ i : Fin (N + 1), ((S.cascadeParameterLaw K N).prod ν) (S.censoredGenieGoodEvent K N h A T i)ᶜ := by
  have hsub : (S.terminalFlatEvent K N h A T (Fin.last N))ᶜ ⊆
      ⋃ i : Fin (N + 1), (S.censoredGenieGoodEvent K N h A T i)ᶜ := by
    intro p hp
    by_contra hn
    simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hn
    exact hp (S.terminalFlat_of_genie_events K N h A T hT hn)
  exact (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)

end RandomizedFO2003.FiniteSpectralDesign
