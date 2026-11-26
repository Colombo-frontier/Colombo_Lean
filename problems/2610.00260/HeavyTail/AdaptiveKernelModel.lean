import HeavyTail.OracleModel
import HeavyTail.AdaptiveKernelRandomized

/-!
Randomized policies may depend on public data, but their types have no private
instance argument. Their arbitrary seed is independent of fresh responses in
the recursively constructed execution law. This file uses exactly T raw calls;
equivalence with almost-sure stopping before T is a separate theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HeavyTail
universe u

namespace AdaptiveKernel

def History.replies {Seed Reply : Type u} : (n : ℕ) → History Seed Reply n → List Reply
  | 0, _ => []
  | n + 1, h => History.replies n h.1 ++ [h.2]

theorem History.replies_length {Seed Reply : Type u} (n : ℕ) (h : History Seed Reply n) :
    (History.replies n h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [History.replies, List.length_append, List.length_singleton, ih]

theorem Policy.outputLaw_zero {Seed Reply Query Output : Type u}
    [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace Query] [MeasurableSpace Output]
    (A : Policy Seed Query Reply Output 0) (μ : Measure Seed) (K : Kernel Query Reply) :
    A.outputLaw μ K = μ.map A.output := rfl

end AdaptiveKernel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

abbrev PublicPolicy (B : PublicProblem E θ) :=
  AdaptiveKernel.RandomizedPolicy B.X E B.X θ.T

namespace PublicPolicy
variable {B : PublicProblem E θ}

def outputLaw (A : PublicPolicy B) (I : PrivateInstance B) : Measure B.X :=
  A.strategy.outputLaw A.seedLaw I.oracle

instance outputLaw_probability (A : PublicPolicy B) (I : PrivateInstance B) :
    IsProbabilityMeasure (PublicPolicy.outputLaw A I) := by
  unfold outputLaw
  infer_instance

theorem query_feasible (A : PublicPolicy B) (n : ℕ)
    (history : AdaptiveKernel.History A.Seed E n) :
    ((A.strategy.query n history : B.X) : E) ∈ B.X := (A.strategy.query n history).property

theorem output_feasible (A : PublicPolicy B)
    (history : AdaptiveKernel.History A.Seed E θ.T) :
    ((A.strategy.output history : B.X) : E) ∈ B.X := (A.strategy.output history).property

theorem raw_call_count (A : PublicPolicy B)
    (history : AdaptiveKernel.History A.Seed E θ.T) :
    (AdaptiveKernel.History.replies θ.T history).length = θ.T :=
  AdaptiveKernel.History.replies_length _ _

/-- A deterministic policy is included without requiring the initial point to
belong to the effective objective domain. -/
def constant (B : PublicProblem E θ) (x : B.X) : PublicPolicy B :=
  AdaptiveKernel.RandomizedPolicy.constant x x

end PublicPolicy

/-- The algorithm receives public data only. In particular, its seed law,
queries and output rule cannot take the hidden f or oracle kernel as inputs. -/
def PublicAlgorithm (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) := ∀ B : PublicProblem E θ, PublicPolicy B

def ModelInstance (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) := Σ B : PublicProblem E θ, PrivateInstance B

def initialPublicAlgorithm : PublicAlgorithm E θ :=
  fun B => PublicPolicy.constant B ⟨B.initial, B.initial_feasible⟩

end HeavyTail
