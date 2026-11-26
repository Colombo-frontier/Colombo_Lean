import NCConcave16991.MixedHaarStabilizerGaussian
import Mathlib.MeasureTheory.Group.Measure

/-! # Exact normalized Haar transport through compact group coordinates -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Continuous surjective group coordinates transport normalized Haar
probability exactly, by the genuine Haar image theorem and uniqueness. -/
theorem compact_haar_probability_transport
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [CompactSpace G] [CompactSpace H] [MeasurableSpace G] [MeasurableSpace H]
    [BorelSpace G] [BorelSpace H]
    (μ : Measure G) (ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [Measure.IsHaarMeasure μ] [Measure.IsHaarMeasure ν]
    (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    MeasurePreserving f μ ν := by
  letI : Measure.IsHaarMeasure (μ.map f) :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure μ f hf hsurj
  exact ⟨hf.measurable,Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩

instance closedSubgroupHaar_isHaar {k : ℕ} (H : Subgroup (Haar.OrthogonalGroup k))
    (hH : IsClosed (H : Set (Haar.OrthogonalGroup k))) :
    Measure.IsHaarMeasure (Haar.subgroupHaarLaw H hH) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior (Haar.subgroupHaarLaw H hH)
    univ isCompact_univ (by simp) (by simp) (by simp)

theorem closedSubgroupHaar_transport {m k : ℕ} (H : Subgroup (Haar.OrthogonalGroup k))
    (hH : IsClosed (H : Set (Haar.OrthogonalGroup k)))
    (f : Haar.OrthogonalGroup m →* H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    MeasurePreserving f (Haar.haarLaw m) (Haar.subgroupHaarLaw H hH) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact compact_haar_probability_transport _ _ f hf hsurj

theorem pointStabilizerHaar_transport {m k : ℕ} (e : SphereSpace k)
    (f : Haar.OrthogonalGroup m →* pointStabilizer e) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    MeasurePreserving f (Haar.haarLaw m) (pointStabilizerLaw e) :=
  closedSubgroupHaar_transport (pointStabilizer e) (pointStabilizer_closed e) f hf hsurj

end NCConcave16991.MixedHaar
