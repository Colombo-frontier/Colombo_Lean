import Nonsmooth.GrunbaumApplication

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem compact_convex_average_mem_interior (K : Set E) (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hinterior : (interior K).Nonempty) :
    (⨍ x in K, x ∂volume) ∈ interior K := by
  obtain ⟨x, hx⟩ := hinterior
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_interior.mem_nhds hx)
  let μ : Measure E := volume.restrict K
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hcompact.measure_lt_top⟩
  have hsub : Metric.closedBall x ε ⊆ K := hball.trans interior_subset
  have hpos : μ (Metric.closedBall x ε) ≠ 0 := by
    rw [show μ = volume.restrict K from rfl, Measure.restrict_apply
      Metric.isClosed_closedBall.measurableSet, inter_eq_left.mpr hsub]
    exact ne_of_gt (Metric.measure_closedBall_pos volume x hε)
  have hav : (⨍ z in Metric.closedBall x ε, z ∂μ) ∈ Metric.closedBall x ε := by
    apply (convex_closedBall x ε).set_average_mem Metric.isClosed_closedBall hpos
      (measure_ne_top μ _)
    · exact ae_restrict_mem Metric.isClosed_closedBall.measurableSet
    · exact continuous_id.continuousOn.integrableOn_compact (isCompact_closedBall x ε)
  exact hconv.average_mem_interior_of_set hpos
    (ae_restrict_mem hcompact.measurableSet)
    (continuous_id.continuousOn.integrableOn_compact hcompact) (hball hav)

open ImportedGeometry.Grunbaum

theorem imported_grunbaum_centroid_interior {d : ℕ} (C : FullDimensionalConvexBody d) :
    C.centroid ∈ interior (C : Set (Euc d)) :=
  compact_convex_average_mem_interior _ C.convex C.isCompact C.interior_nonempty

end
end Nonsmooth


