import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
Generic causal execution with fresh responses from a fixed query-dependent
Markov kernel. History n contains the seed and exactly n replies. Successor
laws are actual composition-products; no transcript law is postulated.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HeavyTail.AdaptiveKernel

universe u v w

def History (Seed Reply : Type u) : ℕ → Type u
  | 0 => Seed
  | n + 1 => History Seed Reply n × Reply

instance historyMeasurable (Seed Reply : Type u) [MeasurableSpace Seed]
    [MeasurableSpace Reply] : (n : ℕ) → MeasurableSpace (History Seed Reply n)
  | 0 => inferInstanceAs (MeasurableSpace Seed)
  | n + 1 => by
      letI := historyMeasurable Seed Reply n
      exact inferInstanceAs (MeasurableSpace (History Seed Reply n × Reply))

/-- Queries use only the replies already received. Queries after T are unused;
their presence avoids casts in the prefix recursion. -/
structure Policy (Seed : Type u) (Query : Type v) (Reply : Type u) (Output : Type w) [MeasurableSpace Seed]
    [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output] (T : ℕ) where
  query : (n : ℕ) → History Seed Reply n → Query
  query_measurable : ∀ n, Measurable (query n)
  output : History Seed Reply T → Output
  output_measurable : Measurable output

namespace Policy
variable {Seed Reply : Type u} {Query : Type v} {Output : Type w} [MeasurableSpace Seed]
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output] {T : ℕ}

def replyKernel (A : Policy Seed Query Reply Output T) (K : Kernel Query Reply) (n : ℕ) :
    Kernel (History Seed Reply n) Reply := K.comap (A.query n) (A.query_measurable n)

theorem replyKernel_apply (A : Policy Seed Query Reply Output T) (K : Kernel Query Reply)
    (n : ℕ) (h : History Seed Reply n) : A.replyKernel K n h = K (A.query n h) := rfl

instance replyKernel_markov (A : Policy Seed Query Reply Output T)
    (K : Kernel Query Reply) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (A.replyKernel K n) := by
  unfold replyKernel
  infer_instance

def historyLaw (A : Policy Seed Query Reply Output T) (μ : Measure Seed)
    (K : Kernel Query Reply) : (n : ℕ) → Measure (History Seed Reply n)
  | 0 => μ
  | n + 1 => (historyLaw A μ K n).compProd (A.replyKernel K n)

theorem historyLaw_zero (A : Policy Seed Query Reply Output T) (μ : Measure Seed)
    (K : Kernel Query Reply) : A.historyLaw μ K 0 = μ := rfl

theorem historyLaw_succ (A : Policy Seed Query Reply Output T) (μ : Measure Seed)
    (K : Kernel Query Reply) (n : ℕ) :
    A.historyLaw μ K (n + 1) = (A.historyLaw μ K n).compProd (A.replyKernel K n) := rfl

instance historyLaw_probability (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] (n : ℕ) : IsProbabilityMeasure (A.historyLaw μ K n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    letI : IsProbabilityMeasure (A.historyLaw μ K n) := ih
    letI : IsMarkovKernel (A.replyKernel K n) := replyKernel_markov A K n
    rw [historyLaw_succ]
    constructor
    exact (Measure.compProd_apply_univ (μ := A.historyLaw μ K n)
      (κ := A.replyKernel K n)).trans (measure_univ)

/-- The next fresh response does not change the distribution of the recorded past. -/
theorem historyLaw_fst (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] (n : ℕ) :
    (A.historyLaw μ K (n + 1)).fst = A.historyLaw μ K n := by
  rw [historyLaw_succ]
  exact Measure.fst_compProd _ _

/-- The defining fresh-kernel identity for every measurable past event and reply event. -/
theorem historyLaw_fresh (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] (n : ℕ) {B : Set (History Seed Reply n)} {C : Set Reply}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    A.historyLaw μ K (n + 1) (B ×ˢ C) =
      ∫⁻ h in B, K (A.query n h) C ∂A.historyLaw μ K n := by
  rw [historyLaw_succ]
  exact Measure.compProd_apply_prod (μ := A.historyLaw μ K n) (κ := A.replyKernel K n) hB hC

/-- Exactly T applications of the raw response kernel are used before output. -/
def outputLaw (A : Policy Seed Query Reply Output T) (μ : Measure Seed)
    (K : Kernel Query Reply) : Measure Output := (A.historyLaw μ K T).map A.output

instance outputLaw_probability (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply)
    [IsMarkovKernel K] : IsProbabilityMeasure (A.outputLaw μ K) := by
  exact isProbabilityMeasure_map A.output_measurable.aemeasurable

theorem outputLaw_apply (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) (K : Kernel Query Reply) {B : Set Output} (hB : MeasurableSet B) :
    A.outputLaw μ K B = A.historyLaw μ K T (A.output ⁻¹' B) :=
  Measure.map_apply A.output_measurable hB

end Policy
end HeavyTail.AdaptiveKernel
