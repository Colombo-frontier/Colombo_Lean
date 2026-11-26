import RandomizedFO2003.NuisanceGeometry
import RandomizedFO2003.NuisanceDesign
import RandomizedFO2003.MeasurableSpanProjection

namespace RandomizedFO2003.SpectralCoordinates

open MeasureTheory

variable {J T : ℕ}

noncomputable def startsSubspace (K : Fin J → ℕ) (g : Fin T → BlockSpace K) (j : Fin J) :
    Submodule ℝ (ComponentSpace K j) :=
  Submodule.span ℝ (Set.range (fun i => slice K j (g i)))

theorem startsSubspace_finrank (K : Fin J → ℕ) (g : Fin T → BlockSpace K) (j : Fin J) :
    Module.finrank ℝ (startsSubspace K g j) ≤ T := by
  simpa only [startsSubspace, Set.finrank, Fintype.card_fin] using
    (finrank_range_le_card (R := ℝ) (fun i => slice K j (g i)))

noncomputable def multiStartKrylovSpace (K : Fin J → ℕ) (node : Fin J → ℝ)
    (g : Fin T → BlockSpace K) : Submodule ℝ (BlockSpace K) :=
  Submodule.span ℝ (Set.range (fun ip : Fin T × Polynomial ℝ =>
    (ip.2.eval₂ (algebraMap ℝ (Module.End ℝ (BlockSpace K))) (diagonal K node)) (g ip.1)))

/-- Even arbitrarily long polynomial preprocessing of the starts remains
inside the direct sum of their blockwise spans. -/
theorem multiStartKrylovSpace_le_nuisanceSpace (K : Fin J → ℕ) (node : Fin J → ℝ)
    (g : Fin T → BlockSpace K) :
    multiStartKrylovSpace K node g ≤ nuisanceSpace K (startsSubspace K g) := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨i, p⟩, rfl⟩ j
  dsimp only
  rw [polynomial_diagonal, slice_diagonal]
  exact (startsSubspace K g j).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

theorem measurable_starts_projection {Ω : Type*} [MeasurableSpace Ω]
    (K : Fin J → ℕ) (g : Ω → Fin T → BlockSpace K)
    (hg : ∀ i, Measurable (fun ω => g ω i)) (j : Fin J) :
    Measurable (fun p : Ω × BlockSpace K =>
      ‖(startsSubspace K (g p.1) j).orthogonalProjection (blockDirection K j p.2)‖) := by
  have hf : ∀ i, Measurable (fun p : Ω × BlockSpace K => slice K j (g p.1 i)) :=
    fun i => (continuous_slice K j).measurable.comp ((hg i).comp measurable_fst)
  exact (measurable_span_projection (fun p : Ω × BlockSpace K => fun i => slice K j (g p.1 i))
    hf (fun p => blockDirection K j p.2)
    ((measurable_blockDirection K j).comp measurable_snd)).norm

end RandomizedFO2003.SpectralCoordinates

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

theorem multiStart_readout (hγ : 0 < γ) {T : ℕ} (K : Fin D.size → ℕ)
    (u : BlockSpace K) (g : Fin T → BlockSpace K)
    (δ η : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j)
    (hproj : ∀ j, ‖(startsSubspace K g j).orthogonalProjection (blockDirection K j u)‖ ≤ η)
    (z : BlockSpace K) (hz : z ∈ shortKrylovSpace K u D.node m ⊔ multiStartKrylovSpace K D.node g) :
    |inner (𝕜 := ℝ) (direction K u D.residual) z| ≤ 4 * (δ + η) * ‖z‖ :=
  D.krylov_nuisance_readout hγ K u (startsSubspace K g) δ η hδ hδhalf hη hηhalf
    hweight hproj z ((sup_le_sup le_rfl (multiStartKrylovSpace_le_nuisanceSpace K D.node g)) hz)

/-- High multiplicity yields uniform readout control for all polynomial
preprocessing of finitely many independent starts. The starts may have any
measurable joint law, including dependent or degenerate coordinates. Their
independence from the sphere vector is encoded by the product measure. -/
theorem independent_high_multiplicity (hγ : 0 < γ)
    (δ η ζ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hζ : 0 < ζ) (T Rmin Nmin : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (g : Ω → Fin T → BlockSpace K),
        (∀ i, Measurable (fun ω => g ω i)) →
        ∃ G : Set (Ω × BlockSpace K), MeasurableSet G ∧
          1 - ENNReal.ofReal ζ ≤ (μ.prod (sphereLaw (BlockSpace K))) G ∧
          ∀ p ∈ G,
            (∀ j, |SpectralCoordinates.weight K p.2 j - D.weight j| ≤ δ * D.weight j) ∧
            (∀ j, ‖(startsSubspace K (g p.1) j).orthogonalProjection (blockDirection K j p.2)‖ ≤ η) ∧
            ‖direction K p.2 D.residual‖ = 1 ∧
            ∀ z ∈ shortKrylovSpace K p.2 D.node m ⊔ multiStartKrylovSpace K D.node (g p.1),
              |inner (𝕜 := ℝ) (direction K p.2 D.residual) z| ≤ 4 * (δ + η) * ‖z‖ := by
  obtain ⟨K, hK, hN, htotal, hunit, hgood⟩ := exists_good_block_geometry
    D.weight D.weight_pos D.weight_sum δ η ζ hδ (by linarith) hη hζ T Rmin Nmin
  refine ⟨K, hK, hN, htotal, hunit, ?_⟩
  intro Ω _ μ _ g hg
  let W := fun ω => startsSubspace K (g ω)
  have hW := measurable_starts_projection K g hg
  refine ⟨blockGoodEvent K D.weight W δ η,
    measurableSet_blockGoodEvent K D.weight W hW δ η,
    hgood Ω μ W hW (fun ω j => startsSubspace_finrank K (g ω) j), ?_⟩
  intro p hp
  have hw := hp.1
  have hproj : ∀ j, ‖(startsSubspace K (g p.1) j).orthogonalProjection
      (blockDirection K j p.2)‖ ≤ η := fun j => (hp.2 j).le
  refine ⟨hw, hproj, ?_, ?_⟩
  · exact direction_norm K p.2 D.residual
      (D.empirical_residual_energy_pos (by positivity) _ δ (by linarith) hw)
  · exact D.multiStart_readout hγ K p.2 (g p.1) δ η hδ.le hδhalf hη.le hηhalf hw hproj

end RandomizedFO2003.FiniteSpectralDesign
