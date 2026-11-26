import RandomizedFO2003.AmbientSpectralKrylov

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical Rotations
open scoped BigOperators ENNReal

universe u

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- Choose multiplicities before the seed space or policy. The good spectral
event now lives on the very same independent ambient history used to simulate
adaptive Haar queries, with all `2n` original starts counted explicitly. -/
theorem ambient_high_multiplicity (hγ : 0 < γ)
    (δ η ζ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hζ : 0 < ζ) (n Rmin Nmin : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∃ G : Set (AmbientPairHistory (BlockSpace K) n (BlockSpace K × Ω)), MeasurableSet G ∧
          1 - ENNReal.ofReal ζ ≤
            (ambientPairHistoryLaw (BlockSpace K) n ((sphereLaw (BlockSpace K)).prod μ)) G ∧
          ∀ p ∈ G,
            (∀ j, |SpectralCoordinates.weight K (AmbientPairHistory.seed (BlockSpace K) n p).1 j -
              D.weight j| ≤ δ * D.weight j) ∧
            (∀ j, ‖(startsSubspace K (AmbientPairHistory.starts (BlockSpace K) n p) j).orthogonalProjection
              (blockDirection K j (AmbientPairHistory.seed (BlockSpace K) n p).1)‖ ≤ η) ∧
            ‖direction K (AmbientPairHistory.seed (BlockSpace K) n p).1 D.residual‖ = 1 ∧
            ∀ z ∈ shortKrylovSpace K (AmbientPairHistory.seed (BlockSpace K) n p).1 D.node m ⊔
                multiStartKrylovSpace K D.node (AmbientPairHistory.starts (BlockSpace K) n p),
              |inner (𝕜 := ℝ) (direction K (AmbientPairHistory.seed (BlockSpace K) n p).1 D.residual) z| ≤
                4 * (δ + η) * ‖z‖ := by
  obtain ⟨K, hK, hN, htotal, hunit, hgood⟩ :=
    D.independent_high_multiplicity hγ δ η ζ hδ hδhalf hη hηhalf hζ (n + n) Rmin Nmin
  refine ⟨K, hK, hN, htotal, hunit, ?_⟩
  intro Ω _ μ _
  let ν := ambientPairHistoryLaw (BlockSpace K) n μ
  obtain ⟨G, hG, hmass, hbound⟩ := hgood (AmbientPairHistory (BlockSpace K) n Ω) ν
    (AmbientPairHistory.starts (BlockSpace K) n) (AmbientPairHistory.starts_measurable n)
  let f := fun p : AmbientPairHistory (BlockSpace K) n (BlockSpace K × Ω) =>
    ((AmbientPairHistory.separate (BlockSpace K) n p).2,
      (AmbientPairHistory.separate (BlockSpace K) n p).1)
  have hf : MeasurePreserving f
      (ambientPairHistoryLaw (BlockSpace K) n ((sphereLaw (BlockSpace K)).prod μ))
      (ν.prod (sphereLaw (BlockSpace K))) :=
    (Measure.measurePreserving_swap (μ := sphereLaw (BlockSpace K)) (ν := ν)).comp
      (AmbientPairHistory.separate_preserving n (sphereLaw (BlockSpace K)) μ)
  refine ⟨f ⁻¹' G, hf.measurable hG, ?_, ?_⟩
  · rwa [hf.measure_preimage hG.nullMeasurableSet]
  · intro p hp
    have hb := hbound (f p) hp
    have hmark : (f p).2 = (AmbientPairHistory.seed (BlockSpace K) n p).1 :=
      AmbientPairHistory.separate_fst (BlockSpace K) n p
    have hstarts : AmbientPairHistory.starts (BlockSpace K) n (f p).1 =
        AmbientPairHistory.starts (BlockSpace K) n p :=
      AmbientPairHistory.starts_separate (BlockSpace K) n p
    rw [hmark, hstarts] at hb
    exact hb

end RandomizedFO2003.FiniteSpectralDesign
