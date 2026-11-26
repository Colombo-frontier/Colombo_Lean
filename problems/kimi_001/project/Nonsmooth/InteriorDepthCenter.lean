import Nonsmooth.GeneralGrunbaumCenter
import Nonsmooth.CentroidInterior

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
open ImportedGeometry.Grunbaum

/-- Every full-dimensional compact convex body in a finite-dimensional real Hilbert space has a quarter-depth center. -/
theorem exists_interior_quarter_depth_center (K : Set E) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hinterior : (interior K).Nonempty) :
    ∃ x ∈ interior K, ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | ℓ z ≤ ℓ x}) := by
  obtain ⟨d, ⟨e⟩⟩ := exists_positive_euclidean_isometry (E := E)
  let C : FullDimensionalConvexBody d :=
    ⟨e '' K, hconv.linear_image e.toLinearMap, hcompact.image e.continuous,
      by
        change (interior (e.toHomeomorph '' K)).Nonempty
        rw [← e.toHomeomorph.image_interior]
        exact hinterior.image e⟩
  let x := e.symm C.centroid
  have hx : x ∈ interior K := by
    have h := imported_grunbaum_centroid_interior C
    change C.centroid ∈ interior (e.toHomeomorph '' K) at h
    rw [← e.toHomeomorph.image_interior] at h
    obtain ⟨z, hz, hez⟩ := h
    change e z = C.centroid at hez
    change e.symm C.centroid ∈ interior K
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
