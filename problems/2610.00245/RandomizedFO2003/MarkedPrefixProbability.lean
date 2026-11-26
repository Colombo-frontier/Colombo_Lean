import RandomizedFO2003.MarkedPrefixEvent
import RandomizedFO2003.InitialCoordinates

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical Rotations
open scoped BigOperators ENNReal

universe u

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- Spectral weights and every eligible query prefix are controlled on one
event, for one multiplicity choice made before any seed space or policy. -/
theorem marked_transcript_prefix_probability (hγ : 0 < γ)
    (δ η ζ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hζ : 0 < ζ) (t Rmin Nmin : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d : ℕ) (plan : MarkedProgram (BlockSpace K) t (BlockSpace K × Ω))
        (F : BlockSpace K × Ω → ExposureFrame (Coordinates (d + markedActionCount t)) (BlockSpace K)),
        ExposureFrame.MeasurableFamily F → (∀ ω, (F ω).KnownSupport) →
        (∀ ω, embeddingComplement (F ω).latent = ⊥) →
        1 - ENNReal.ofReal ζ ≤
          (((sphereLaw (BlockSpace K)).prod μ).prod (haarLaw (Coordinates (d + markedActionCount t)))).map
            (fun p => (plan.compile (continuousDiagonal K D.node) t Prod.fst measurable_fst).run
              (markedActionCount t) ((F p.1).operator p.2) p.1)
            (historyWeightEvent K D.weight t Prod.fst δ ∩
              plan.prefixReadoutEvent K D.residual m t Prod.fst (4 * (δ + η))) := by
  obtain ⟨K, hK, hN, htotal, hunit, hgeometry⟩ :=
    D.ambient_high_multiplicity hγ δ η ζ hδ hδhalf hη hηhalf hζ (markedActionCount t) Rmin Nmin
  refine ⟨K, hK, hN, htotal, hunit, ?_⟩
  intro Ω _ μ _ d plan F hF hsupport hknown
  let σ := (sphereLaw (BlockSpace K)).prod μ
  let ν := ambientPairHistoryLaw (BlockSpace K) (markedActionCount t) σ
  let program := plan.compile (continuousDiagonal K D.node) t Prod.fst measurable_fst
  let B := historyWeightEvent K D.weight t Prod.fst δ ∩
    plan.prefixReadoutEvent K D.residual m t Prod.fst (4 * (δ + η))
  have hB : MeasurableSet B :=
    (measurableSet_historyWeightEvent K D.weight t Prod.fst measurable_fst δ).inter
      (plan.measurableSet_prefixReadoutEvent K D.residual m t Prod.fst measurable_fst _)
  have hsim := program.directAmbientTranscript_measurable d (markedActionCount t) F hF id measurable_id
  obtain ⟨G, hG, hmass, hbound⟩ := hgeometry Ω μ
  have hgood : ∀ᵐ p ∂ν, program.directAmbientGood d (markedActionCount t) F id p :=
    program.directAmbientGood_ae d (markedActionCount t) σ F hF id measurable_id
  obtain ⟨G', hG', hmass', hsub, hpoint⟩ := measurable_good_core ν G hG
    (program.directAmbientGood d (markedActionCount t) F id) hgood
  have hcontained : G' ⊆ program.directAmbientTranscript d (markedActionCount t) F id ⁻¹' B := by
    intro p hp
    constructor
    · intro j
      have hw := (hbound p (hsub hp)).1 j
      have hs := program.directAmbientTranscript_seed d (markedActionCount t) F id p
      simpa only [hs, id_eq] using hw
    · exact plan.simulation_mem_prefixReadoutEvent K D.node D.residual d t m Prod.fst measurable_fst
        F id (4 * (δ + η)) p (hsupport _) (hknown _) (hpoint p hp) ((hbound p (hsub hp)).2.2.2)
  have hlaw := program.directAmbientTranscript_law d (markedActionCount t) σ F hF id measurable_id
  change 1 - ENNReal.ofReal ζ ≤
    (σ.prod (haarLaw (Coordinates (d + markedActionCount t)))).map
      (fun p => program.run (markedActionCount t) ((F p.1).operator p.2) (id p.1)) B
  rw [hlaw, Measure.map_apply hsim hB]
  exact hmass.trans (hmass' ▸ measure_mono hcontained)

/-- The simultaneous prefix barrier on the original Haar operator. No
coordinate frame, legal-schedule certificate, or independent-start premise
is left to the caller. The retained weight event uses the same K. -/
theorem marked_haar_prefix_probability (hγ : 0 < γ)
    (δ η ζ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hζ : 0 < ζ) (t Rmin Nmin : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ markedActionCount t ≤ ∑ j, K j ∧
      0 < ∑ j, K j ∧ (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (plan : MarkedProgram (BlockSpace K) t (BlockSpace K × Ω)),
        1 - ENNReal.ofReal ζ ≤
          (((sphereLaw (BlockSpace K)).prod μ).prod (haarLaw (BlockSpace K))).map
            (fun p => (plan.compile (continuousDiagonal K D.node) t Prod.fst measurable_fst).run
              (markedActionCount t) (p.2 : BlockSpace K →L[ℝ] BlockSpace K) p.1)
            (historyWeightEvent K D.weight t Prod.fst δ ∩
              plan.prefixReadoutEvent K D.residual m t Prod.fst (4 * (δ + η))) := by
  obtain ⟨K, hK, hN, htotal, hunit, hprob⟩ :=
    D.marked_transcript_prefix_probability hγ δ η ζ hδ hδhalf hη hηhalf hζ t Rmin
      (max Nmin (markedActionCount t))
  have hdim : markedActionCount t ≤ ∑ j, K j := (Nat.le_max_right _ _).trans hN
  refine ⟨K, hK, (Nat.le_max_left _ _).trans hN, hdim, htotal, hunit, ?_⟩
  intro Ω _ μ _ plan
  let d := (∑ j, K j) - markedActionCount t
  have hfinrank : Module.finrank ℝ (BlockSpace K) = d + markedActionCount t := by
    dsimp only [d]
    rw [Nat.sub_add_cancel hdim]
    simp [BlockSpace]
  let V := initialCoordinates (E := BlockSpace K) (d + markedActionCount t) hfinrank
  let F := fun _ : BlockSpace K × Ω => (ExposureFrame.initial : ExposureFrame (BlockSpace K) (BlockSpace K)).reindex V
  have hF : ExposureFrame.MeasurableFamily F := ExposureFrame.measurable_initial.reindex V
  have hs : ∀ ω, (F ω).KnownSupport := fun _ => ExposureFrame.initial_knownSupport.reindex V
  have hl : ∀ ω, embeddingComplement (F ω).latent = ⊥ := fun _ => initial_reindex_latentComplement V
  have hp := hprob Ω μ d plan F hF hs hl
  have heq := (plan.compile (continuousDiagonal K D.node) t Prod.fst measurable_fst).initial_coordinate_law
    d (markedActionCount t) ((sphereLaw (BlockSpace K)).prod μ) V
  rw [heq]
  exact hp

end RandomizedFO2003.FiniteSpectralDesign
