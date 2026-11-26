import FreshGradientMinimax.Oracle
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Basic

/-! Unrestricted randomized algorithms and their finite transcript laws.
Every history stores all query--response pairs. The seed is drawn once and is
retained unchanged. Responses are drawn from the same fixed kernel at each
adaptive query. No norm, span, support or output-query restriction is imposed. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

abbrev History (dx dy n : ℕ) := Fin n → Joint dx dy × Joint dx dy
abbrev RunState (dx dy : ℕ) (Seed : Type*) (n : ℕ) := Seed × History dx dy n

structure Algorithm (dx dy : ℕ) (Seed : Type*) [MeasurableSpace Seed] where
  query : (n : ℕ) → RunState dx dy Seed n → Joint dx dy
  output : (n : ℕ) → RunState dx dy Seed n → Euclid dx
  query_measurable : ∀ n, Measurable (query n)
  output_measurable : ∀ n, Measurable (output n)

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)

def initial (seed : Seed) : RunState dx dy Seed 0 := (seed, Fin.elim0)

theorem initial_measurable : Measurable (initial (dx := dx) (dy := dy) (Seed := Seed)) := by
  exact measurable_id.prodMk measurable_const

def append (n : ℕ) (sr : RunState dx dy Seed n × Joint dx dy) : RunState dx dy Seed (n + 1) :=
  (sr.1.1, Fin.snoc sr.1.2 (A.query n sr.1, sr.2))

theorem append_measurable (n : ℕ) : Measurable (A.append n) := by
  apply (measurable_fst.comp measurable_fst).prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [append, Fin.snoc_last]
    exact ((A.query_measurable n).comp measurable_fst).prodMk measurable_snd
  · simp only [append, Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

def responseKernel (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    Kernel (RunState dx dy Seed n) (Joint dx dy) :=
  K.comap (A.query n) (A.query_measurable n)

instance responseKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (A.responseKernel K n) := by unfold responseKernel; infer_instance

def stepKernel (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    Kernel (RunState dx dy Seed n) (RunState dx dy Seed (n + 1)) :=
  (Kernel.id ×ₖ A.responseKernel K n).map (A.append n)

instance stepKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (A.stepKernel K n) :=
  Kernel.IsMarkovKernel.map _ (A.append_measurable n)

def historyKernel (A : Algorithm dx dy Seed) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (n : ℕ) → Kernel Seed (RunState dx dy Seed n)
  | 0 => Kernel.deterministic initial initial_measurable
  | n + 1 => A.stepKernel K n ∘ₖ A.historyKernel K n

instance historyKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (A.historyKernel K n) := by
  induction n with
  | zero => unfold historyKernel; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (A.stepKernel K n ∘ₖ A.historyKernel K n)
    infer_instance

def outputKernel (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) : Kernel Seed (Euclid dx) :=
  (A.historyKernel K n).map (A.output n)

instance outputKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (A.outputKernel K n) :=
  Kernel.IsMarkovKernel.map _ (A.output_measurable n)

def outputLaw (ν : Measure Seed) (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    Measure (Euclid dx) := A.outputKernel K n ∘ₘ ν

instance outputLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (A.outputLaw ν K n) := by unfold outputLaw; infer_instance

theorem zero_query_law_independent (ν : Measure Seed)
    (K K' : Kernel (Joint dx dy) (Joint dx dy)) :
    A.outputLaw ν K 0 = A.outputLaw ν K' 0 := rfl

theorem queried_response_law (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ)
    (s : RunState dx dy Seed n) : A.responseKernel K n s = K (A.query n s) := rfl

theorem append_retains_seed (n : ℕ) (sr : RunState dx dy Seed n × Joint dx dy) :
    (A.append n sr).1 = sr.1.1 := rfl

theorem append_retains_history (n : ℕ) (sr : RunState dx dy Seed n × Joint dx dy) (i : Fin n) :
    (A.append n sr).2 i.castSucc = sr.1.2 i := by simp [append]

theorem append_records_query_response (n : ℕ) (sr : RunState dx dy Seed n × Joint dx dy) :
    (A.append n sr).2 (Fin.last n) = (A.query n sr.1, sr.2) := by simp [append]

end Algorithm

structure RandomizedAlgorithm (dx dy : ℕ) where
  Seed : Type
  [measurableSeed : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [seedProbability : IsProbabilityMeasure seedLaw]
  policy : Algorithm dx dy Seed

attribute [instance] RandomizedAlgorithm.measurableSeed RandomizedAlgorithm.seedProbability

namespace RandomizedAlgorithm
variable {dx dy : ℕ} (A : RandomizedAlgorithm dx dy)

def outputLaw (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) : Measure (Euclid dx) :=
  A.policy.outputLaw A.seedLaw K n

instance outputLaw_probability (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (A.outputLaw K n) := by unfold outputLaw; infer_instance

end RandomizedAlgorithm
end FreshGradientMinimax
