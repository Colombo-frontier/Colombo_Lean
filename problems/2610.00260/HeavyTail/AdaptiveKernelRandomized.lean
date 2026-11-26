import HeavyTail.AdaptiveKernelExecution

/-! Arbitrary measurable random seeds for the generic fresh-kernel execution. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
universe u v w

structure RandomizedPolicy (Query : Type v) (Reply : Type u) (Output : Type w)
    [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output] (T : ℕ) where
  Seed : Type u
  seedSpace : MeasurableSpace Seed
  seedLaw : @Measure Seed seedSpace
  seed_probability : @IsProbabilityMeasure Seed seedSpace seedLaw
  strategy : @Policy Seed Query Reply Output seedSpace _ _ _ T

attribute [instance] RandomizedPolicy.seedSpace RandomizedPolicy.seed_probability

namespace RandomizedPolicy
variable {Query : Type v} {Reply : Type u} {Output : Type w}
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output] {T : ℕ}

def outputLaw (A : RandomizedPolicy Query Reply Output T) (K : Kernel Query Reply) :
    Measure Output := A.strategy.outputLaw A.seedLaw K

instance outputLaw_probability (A : RandomizedPolicy Query Reply Output T)
    (K : Kernel Query Reply) [IsMarkovKernel K] : IsProbabilityMeasure (A.outputLaw K) := by
  unfold outputLaw
  infer_instance

def constant (x : Query) (y : Output) : RandomizedPolicy Query Reply Output T where
  Seed := PUnit.{u + 1}
  seedSpace := ⊤
  seedLaw := Measure.dirac PUnit.unit
  seed_probability := by infer_instance
  strategy := {
    query := fun _ _ => x
    query_measurable := fun _ => measurable_const
    output := fun _ => y
    output_measurable := measurable_const }

end RandomizedPolicy
end HeavyTail.AdaptiveKernel
