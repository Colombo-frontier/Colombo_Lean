import AdaptiveSphereAction
import AdaptiveSphereOrbit

/-! Removing rotation-dependent exceptional sets from actual conditional-law
identities by countable density and proved weak continuity of pushforwards. -/
open MeasureTheory Set Filter Topology
open scoped Matrix

namespace Task006.AdaptiveSphereKernel
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereAction Task006.AdaptiveSphereOrbit
noncomputable section

theorem ae_all_orthogonal_invariance_of_each
    {H : Type*} [MeasurableSpace H] (ν : Measure H) (n : ℕ)
    (κ : H → Measure (E n)) (hprob : ∀ h, IsProbabilityMeasure (κ h))
    (hrot : ∀ g : OrthogonalGroup n,
      ∀ᵐ h ∂ν, Measure.map (action g) (κ h) = κ h) :
    ∀ᵐ h ∂ν, ∀ g : OrthogonalGroup n, Measure.map (action g) (κ h) = κ h := by
  have hall : ∀ᵐ h ∂ν, ∀ l : ℕ,
      Measure.map (action (TopologicalSpace.denseSeq (OrthogonalGroup n) l)) (κ h) = κ h := by
    rw [ae_all_iff]
    exact fun l => hrot (TopologicalSpace.denseSeq (OrthogonalGroup n) l)
  filter_upwards [hall] with h hh
  letI : IsProbabilityMeasure (κ h) := hprob h
  intro g
  have hg : g ∈ closure (Set.range (TopologicalSpace.denseSeq (OrthogonalGroup n))) :=
    (TopologicalSpace.denseRange_denseSeq (OrthogonalGroup n)) g
  obtain ⟨f,hf,hlim⟩ := mem_closure_iff_seq_limit.mp hg
  have hmp (l : ℕ) : MeasurePreserving (action (f l)) (κ h) (κ h) := by
    obtain ⟨m,hm⟩ := hf l
    refine ⟨(action (f l)).continuous.measurable,?_⟩
    rw [← hm]
    exact hh m
  have hconv (x : E n) : Tendsto (fun l => action (f l) x) atTop (𝓝 (action g x)) := by
    have hc : Continuous (fun Q : OrthogonalGroup n => action Q x) := by
      have hr := (action_joint_continuous (d := n)).comp
        (continuous_id.prodMk continuous_const : Continuous (fun Q : OrthogonalGroup n => (Q,x)))
      simpa only [Function.comp_def,id_eq] using hr
    exact (hc.tendsto g).comp hlim
  exact (measurePreserving_of_pointwise_limit (fun l => action (f l)) hmp
    (action g) (action g).continuous.measurable hconv).map_eq

#print axioms ae_all_orthogonal_invariance_of_each
end
end Task006.AdaptiveSphereKernel
