import Nonsmooth.GrunbaumApplication

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
open ImportedGeometry.Grunbaum

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_positive_euclidean_isometry : ∃ d : ℕ, Nonempty (E ≃ₗᵢ[ℝ] Euc d) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Module.finrank_pos : 0 < Module.finrank ℝ E))
  refine ⟨d, ?_⟩
  change Module.finrank ℝ E = d + 1 at hd
  change Nonempty (E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  rw [← hd]
  exact ⟨(stdOrthonormalBasis ℝ E).repr⟩

omit [Nontrivial E] in
theorem isometry_volume_image {d : ℕ} (e : E ≃ₗᵢ[ℝ] Euc d) (G : Set E) (hG : MeasurableSet G) :
    volume (e '' G) = volume G := by
  have heq : e.symm ⁻¹' G = e '' G := by
    ext z
    constructor
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [← heq]
  exact e.symm.measurePreserving.measure_preimage hG.nullMeasurableSet

/-- Every full-dimensional compact convex body in a finite-dimensional real Hilbert space has a quarter-depth center. -/
theorem exists_quarter_depth_center (K : Set E) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hinterior : (interior K).Nonempty) :
    ∃ x ∈ K, ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | ℓ z ≤ ℓ x}) := by
  obtain ⟨d, ⟨e⟩⟩ := exists_positive_euclidean_isometry (E := E)
  let C : FullDimensionalConvexBody d :=
    ⟨e '' K, hconv.linear_image e.toLinearMap, hcompact.image e.continuous,
      by
        change (interior (e.toHomeomorph '' K)).Nonempty
        rw [← e.toHomeomorph.image_interior]
        exact hinterior.image e⟩
  let x := e.symm C.centroid
  have hx : x ∈ K := by
    obtain ⟨z, hz, hez⟩ := imported_grunbaum_centroid_mem C
    change e.symm C.centroid ∈ K
    rw [← hez, e.symm_apply_apply]
    exact hz
  refine ⟨x, hx, ?_⟩
  intro ℓ hℓ
  let L : Euc d →L[ℝ] ℝ := ℓ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : L ≠ 0 := by
    intro hz
    apply hℓ
    ext z
    have h := congrArg (fun q : Euc d →L[ℝ] ℝ => q (e z)) hz
    change ℓ (e.symm (e z)) = 0 at h
    simpa using h
  have h := imported_grunbaum_centroid_quarter C L hL
  have hset : ((C : Set (Euc d)) ∩ {z | L z ≤ L C.centroid}) = e '' (K ∩ {z | ℓ z ≤ ℓ x}) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      simpa [L, x] using hz
    · rintro ⟨y, ⟨hy, hle⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by simpa [L, x] using hle⟩
  rw [hset, isometry_volume_image e _ (hcompact.measurableSet.inter
    (measurableSet_le ℓ.measurable measurable_const))] at h
  change ENNReal.ofReal (1 / 4 : ℝ) * volume (e '' K) ≤ _ at h
  rw [isometry_volume_image e K hcompact.measurableSet] at h
  exact h

end
end Nonsmooth
