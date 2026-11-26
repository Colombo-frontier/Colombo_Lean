import HeavyTail.AdaptiveKernelConcatenation

/-! Public dummy queries pad a constructed policy to an arbitrary larger
deterministic budget without changing its output law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
universe u v w

namespace History
variable {Seed Reply : Type u} [MeasurableSpace Seed] [MeasurableSpace Reply]

def seed : (n : ℕ) → History Seed Reply n → Seed
  | 0 => id
  | n + 1 => fun h => seed n h.1

theorem seed_measurable (n : ℕ) : Measurable (seed (Seed := Seed) (Reply := Reply) n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst

end History

namespace Policy
variable {Seed Reply : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace Query]
  [MeasurableSpace Output] {m T : ℕ}

theorem historyLaw_seed (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] (n : ℕ) : (A.historyLaw μ K n).map (History.seed n) = μ := by
  induction n with
  | zero => exact Measure.map_id
  | succ n ih =>
    change (A.historyLaw μ K (n + 1)).map (History.seed n ∘ Prod.fst) = μ
    rw [← Measure.map_map (History.seed_measurable n) measurable_fst]
    change (A.historyLaw μ K (n + 1)).fst.map (History.seed n) = μ
    rw [historyLaw_fst, ih]

def dummy (q : Query) (N : ℕ) : Policy Seed Query Reply Seed N where
  query _ _ := q
  query_measurable _ := measurable_const
  output := History.seed N
  output_measurable := History.seed_measurable N

theorem dummy_outputLaw (q : Query) (N : ℕ) (μ : Measure Seed)
    [IsProbabilityMeasure μ] (K : Kernel Query Reply) [IsMarkovKernel K] :
    (dummy (Seed := Seed) q N).outputLaw μ K = μ :=
  (dummy q N).historyLaw_seed μ K N

def castHorizon (A : Policy Seed Query Reply Output m) (h : m = T) :
    Policy Seed Query Reply Output T where
  query := A.query
  query_measurable := A.query_measurable
  output := A.output ∘ History.cast h.symm
  output_measurable := A.output_measurable.comp (History.cast_measurable h.symm)

theorem castHorizon_outputLaw (A : Policy Seed Query Reply Output m) (h : m = T)
    (μ : Measure Seed) (K : Kernel Query Reply) :
    (A.castHorizon h).outputLaw μ K = A.outputLaw μ K := by
  subst T
  rfl

def pad {Out : Type u} [MeasurableSpace Out]
    (A : Policy Seed Query Reply Out m) (q : Query) (h : m ≤ T) :
    Policy Seed Query Reply Out T :=
  (A.chain (dummy q (T - m))).castHorizon (Nat.add_sub_of_le h)

theorem pad_outputLaw {Out : Type u} [MeasurableSpace Out]
    (A : Policy Seed Query Reply Out m) (q : Query) (h : m ≤ T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply) [IsMarkovKernel K] :
    (A.pad q h).outputLaw μ K = A.outputLaw μ K := by
  rw [pad, castHorizon_outputLaw, chain_outputLaw, dummy_outputLaw]

end Policy
end HeavyTail.AdaptiveKernel
