import RandomizedFO2003.InitialCoordinates

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical Rotations
open scoped BigOperators ENNReal

universe u

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The single-block randomized readout bound for actual adaptive marked matrix
access. Dimension and multiplicities precede the arbitrary probability seed
space and full-history policy. All frames and independent innovations have
been constructed or eliminated from this statement. -/
theorem marked_haar_readout_probability (hγ : 0 < γ)
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
            (plan.readoutEvent K D.residual m t Prod.fst (4 * (δ + η))) := by
  obtain ⟨K, hK, hN, htotal, hunit, hprob⟩ :=
    D.marked_transcript_readout_probability hγ δ η ζ hδ hδhalf hη hηhalf hζ t Rmin
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
