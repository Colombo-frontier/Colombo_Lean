import HeavyTail.AdaptiveKernelConcatenation

/-! Replacing an algorithm's initial seed by a measurable function preserves
the genuine execution law. In particular, a random-center policy conditioned
at a fixed public center is realized by a constant seed map. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel.Policy
universe u v w
variable {Seed Seed' Reply : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Seed'] [MeasurableSpace Reply]
  [MeasurableSpace Query] [MeasurableSpace Output] {T : ℕ}

theorem extensionality {A B : Policy Seed Query Reply Output T}
    (hq : ∀ n, A.query n = B.query n) (ho : A.output = B.output) : A = B := by
  cases A
  cases B
  cases funext hq
  cases ho
  rfl

def precomposeSeed (A : Policy Seed Query Reply Output T) (f : Seed' → Seed)
    (hf : Measurable f) : Policy Seed' Query Reply Output T where
  query n := A.query n ∘ History.mapSeed f n
  query_measurable n := (A.query_measurable n).comp (History.mapSeed_measurable hf n)
  output := A.output ∘ History.mapSeed f T
  output_measurable := A.output_measurable.comp (History.mapSeed_measurable hf T)

theorem precomposeSeed_historyLaw (A : Policy Seed Query Reply Output T)
    (f : Seed' → Seed) (hf : Measurable f) (μ : Measure Seed') [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] (n : ℕ) :
    ((A.precomposeSeed f hf).historyLaw μ K n).map (History.mapSeed f n) =
      A.historyLaw (μ.map f) K n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (((A.precomposeSeed f hf).historyLaw μ K n).compProd
      ((A.precomposeSeed f hf).replyKernel K n)).map
      (fun z => (History.mapSeed f n z.1, z.2)) =
        (A.historyLaw (μ.map f) K n).compProd (A.replyKernel K n)
    have hK : (A.precomposeSeed f hf).replyKernel K n =
        (A.replyKernel K n).comap (History.mapSeed f n) (History.mapSeed_measurable hf n) := rfl
    rw [hK, compProd_comap_map _ _ _ (History.mapSeed_measurable hf n), ih]

theorem precomposeSeed_outputLaw (A : Policy Seed Query Reply Output T)
    (f : Seed' → Seed) (hf : Measurable f) (μ : Measure Seed') [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] :
    (A.precomposeSeed f hf).outputLaw μ K = A.outputLaw (μ.map f) K := by
  change ((A.precomposeSeed f hf).historyLaw μ K T).map
    (A.output ∘ History.mapSeed f T) = _
  rw [← Measure.map_map A.output_measurable (History.mapSeed_measurable hf T),
    precomposeSeed_historyLaw]
  rfl

theorem precomposeSeed_dirac_outputLaw (A : Policy Seed Query Reply Output T)
    (f : Seed' → Seed) (hf : Measurable f) (s : Seed')
    (K : Kernel Query Reply) [IsMarkovKernel K] :
    (A.precomposeSeed f hf).outputLaw (Measure.dirac s) K =
      A.outputLaw (Measure.dirac (f s)) K := by
  rw [precomposeSeed_outputLaw, Measure.map_dirac hf]

end HeavyTail.AdaptiveKernel.Policy
