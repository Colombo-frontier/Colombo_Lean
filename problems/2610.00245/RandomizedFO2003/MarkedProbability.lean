import RandomizedFO2003.MarkedReadoutEvent
import RandomizedFO2003.AmbientMultiplicity

namespace RandomizedFO2003

open MeasureTheory

/-- Remove a measurable null superset of the exceptional executions, keeping
the exact mass of a given good event and making its conclusions pointwise. -/
theorem measurable_good_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Set Ω) (hG : MeasurableSet G) (P : Ω → Prop) (hP : ∀ᵐ p ∂μ, P p) :
    ∃ G' : Set Ω, MeasurableSet G' ∧ μ G' = μ G ∧ G' ⊆ G ∧ ∀ p ∈ G', P p := by
  let Z := toMeasurable μ {p | ¬ P p}
  have hZ : μ Z = 0 := by
    rw [show Z = toMeasurable μ {p | ¬ P p} from rfl, measure_toMeasurable]
    exact ae_iff.mp hP
  refine ⟨G \ Z, hG.diff (measurableSet_toMeasurable μ _), measure_diff_null hZ,
    fun _ hp => hp.1, ?_⟩
  intro p hp
  by_contra hn
  exact hp.2 (subset_toMeasurable μ _ hn)

end RandomizedFO2003

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical Rotations
open scoped BigOperators ENNReal

universe u

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- A uniform probability bound on the actual full transcript of every
concrete marked matrix strategy. Multiplicities are chosen before the seed
space or policy; no legality, independent-start, or span assumption on its
queries remains. Only the initial coordinate-frame conditions are supplied. -/
theorem marked_transcript_readout_probability (hγ : 0 < γ)
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
            (plan.readoutEvent K D.residual m t Prod.fst (4 * (δ + η))) := by
  obtain ⟨K, hK, hN, htotal, hunit, hgeometry⟩ :=
    D.ambient_high_multiplicity hγ δ η ζ hδ hδhalf hη hηhalf hζ (markedActionCount t) Rmin Nmin
  refine ⟨K, hK, hN, htotal, hunit, ?_⟩
  intro Ω _ μ _ d plan F hF hsupport hknown
  let σ := (sphereLaw (BlockSpace K)).prod μ
  let ν := ambientPairHistoryLaw (BlockSpace K) (markedActionCount t) σ
  let program := plan.compile (continuousDiagonal K D.node) t Prod.fst measurable_fst
  let B := plan.readoutEvent K D.residual m t Prod.fst (4 * (δ + η))
  have hB : MeasurableSet B := plan.measurableSet_readoutEvent K D.residual m t Prod.fst measurable_fst _
  have hsim := program.directAmbientTranscript_measurable d (markedActionCount t) F hF id measurable_id
  obtain ⟨G, hG, hmass, hbound⟩ := hgeometry Ω μ
  have hgood : ∀ᵐ p ∂ν, program.directAmbientGood d (markedActionCount t) F id p :=
    program.directAmbientGood_ae d (markedActionCount t) σ F hF id measurable_id
  obtain ⟨G', hG', hmass', hsub, hpoint⟩ := measurable_good_core ν G hG
    (program.directAmbientGood d (markedActionCount t) F id) hgood
  have hcontained : G' ⊆ program.directAmbientTranscript d (markedActionCount t) F id ⁻¹' B := by
    intro p hp
    exact plan.simulation_mem_readoutEvent K D.node D.residual d t m Prod.fst measurable_fst
      F id (4 * (δ + η)) p (hsupport _) (hknown _) (hpoint p hp) ((hbound p (hsub hp)).2.2.2)
  have hlaw := program.directAmbientTranscript_law d (markedActionCount t) σ F hF id measurable_id
  change 1 - ENNReal.ofReal ζ ≤
    (σ.prod (haarLaw (Coordinates (d + markedActionCount t)))).map
      (fun p => program.run (markedActionCount t) ((F p.1).operator p.2) (id p.1)) B
  rw [hlaw, Measure.map_apply hsim hB]
  exact hmass.trans (hmass' ▸ measure_mono hcontained)

end RandomizedFO2003.FiniteSpectralDesign
