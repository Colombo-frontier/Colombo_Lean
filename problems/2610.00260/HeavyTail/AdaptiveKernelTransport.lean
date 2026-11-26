import HeavyTail.AdaptiveKernelRandomized

/-! Exact transport of causal policies along measurable query/output maps.
In particular, feasible-subtype policies can be viewed as ambient-space policies
without changing their observed histories or exposing private information. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
universe u v v' w w'

namespace Policy
variable {Seed Reply : Type u} {Query : Type v} {Query' : Type v'}
  {Output : Type w} {Output' : Type w'} [MeasurableSpace Seed] [MeasurableSpace Reply]
  [MeasurableSpace Query] [MeasurableSpace Query'] [MeasurableSpace Output]
  [MeasurableSpace Output'] {T : ℕ}

def mapQueryOutput (A : Policy Seed Query Reply Output T)
    (q : Query → Query') (hq : Measurable q) (g : Output → Output') (hg : Measurable g) :
    Policy Seed Query' Reply Output' T where
  query n h := q (A.query n h)
  query_measurable n := hq.comp (A.query_measurable n)
  output h := g (A.output h)
  output_measurable := hg.comp A.output_measurable

theorem historyLaw_mapQueryOutput (A : Policy Seed Query Reply Output T)
    (q : Query → Query') (hq : Measurable q) (g : Output → Output') (hg : Measurable g)
    (μ : Measure Seed) (K : Kernel Query' Reply) (n : ℕ) :
    (A.mapQueryOutput q hq g hg).historyLaw μ K n = A.historyLaw μ (K.comap q hq) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [historyLaw_succ, ih]
    rfl

theorem outputLaw_mapQueryOutput (A : Policy Seed Query Reply Output T)
    (q : Query → Query') (hq : Measurable q) (g : Output → Output') (hg : Measurable g)
    (μ : Measure Seed) (K : Kernel Query' Reply) :
    (A.mapQueryOutput q hq g hg).outputLaw μ K = (A.outputLaw μ (K.comap q hq)).map g := by
  unfold outputLaw
  rw [historyLaw_mapQueryOutput]
  exact (Measure.map_map hg A.output_measurable).symm

end Policy

namespace RandomizedPolicy
variable {Reply : Type u} {Query : Type v} {Query' : Type v'}
  {Output : Type w} {Output' : Type w'} [MeasurableSpace Reply]
  [MeasurableSpace Query] [MeasurableSpace Query'] [MeasurableSpace Output]
  [MeasurableSpace Output'] {T : ℕ}

def mapQueryOutput (A : RandomizedPolicy Query Reply Output T)
    (q : Query → Query') (hq : Measurable q) (g : Output → Output') (hg : Measurable g) :
    RandomizedPolicy Query' Reply Output' T where
  Seed := A.Seed
  seedSpace := A.seedSpace
  seedLaw := A.seedLaw
  seed_probability := A.seed_probability
  strategy := A.strategy.mapQueryOutput q hq g hg

theorem outputLaw_mapQueryOutput (A : RandomizedPolicy Query Reply Output T)
    (q : Query → Query') (hq : Measurable q) (g : Output → Output') (hg : Measurable g)
    (K : Kernel Query' Reply) :
    (A.mapQueryOutput q hq g hg).outputLaw K = (A.outputLaw (K.comap q hq)).map g :=
  A.strategy.outputLaw_mapQueryOutput q hq g hg A.seedLaw K

end RandomizedPolicy
end HeavyTail.AdaptiveKernel
