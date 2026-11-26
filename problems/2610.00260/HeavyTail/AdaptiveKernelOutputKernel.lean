import HeavyTail.AdaptiveKernelExecution
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! The actual finite execution is a Markov kernel in its initial seed.
This supplies the measurable transition law needed when the seed is the
random center produced by a preceding localization stage. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
universe u v w

namespace Policy
variable {Seed Reply : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace Query]
  [MeasurableSpace Output] {T : ℕ}

def historyKernel (A : Policy Seed Query Reply Output T) (K : Kernel Query Reply) :
    (n : ℕ) → Kernel Seed (History Seed Reply n)
  | 0 => Kernel.id
  | n + 1 => (Kernel.id ×ₖ A.replyKernel K n) ∘ₖ historyKernel A K n

instance historyKernel_markov (A : Policy Seed Query Reply Output T)
    (K : Kernel Query Reply) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (A.historyKernel K n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel Seed Seed))
  | succ n ih =>
    letI := ih
    change IsMarkovKernel ((Kernel.id ×ₖ A.replyKernel K n) ∘ₖ A.historyKernel K n)
    infer_instance

theorem historyLaw_eq_historyKernel (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] (n : ℕ) :
    A.historyLaw μ K n = A.historyKernel K n ∘ₘ μ := by
  induction n with
  | zero => exact Measure.id_comp.symm
  | succ n ih =>
    rw [historyLaw_succ, Measure.compProd_eq_comp_prod, ih, Measure.comp_assoc]
    rfl

def outputKernel (A : Policy Seed Query Reply Output T) (K : Kernel Query Reply) :
    Kernel Seed Output := (A.historyKernel K T).map A.output

instance outputKernel_markov (A : Policy Seed Query Reply Output T)
    (K : Kernel Query Reply) [IsMarkovKernel K] : IsMarkovKernel (A.outputKernel K) := by
  unfold outputKernel
  exact Kernel.IsMarkovKernel.map _ A.output_measurable

theorem outputLaw_eq_outputKernel (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] : A.outputLaw μ K = A.outputKernel K ∘ₘ μ := by
  rw [outputLaw, historyLaw_eq_historyKernel, Measure.map_comp μ _ A.output_measurable]
  rfl

theorem outputKernel_apply (A : Policy Seed Query Reply Output T)
    (K : Kernel Query Reply) [IsMarkovKernel K] (s : Seed) :
    A.outputKernel K s = A.outputLaw (Measure.dirac s) K := by
  rw [outputLaw_eq_outputKernel, Measure.dirac_bind (A.outputKernel K).measurable]

end Policy
end HeavyTail.AdaptiveKernel
