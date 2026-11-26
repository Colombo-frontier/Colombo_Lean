import HeavyTail.AdaptiveKernelStopping
import HeavyTail.ModelQuantile

/-! Minimax over genuine bounded causal stopping policies equals the minimax
over exactly T raw calls. Both policy classes depend only on public data. The
padding map is uniform in the unknown objective and response kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

structure AtMostPublicPolicy (B : PublicProblem E θ) where
  base : PublicPolicy B
  stopping : AdaptiveKernel.StoppingRule base.Seed E B.X
  call_budget : ∀ I : PrivateInstance B,
    (stopping.liveLaw base.strategy base.seedLaw I.oracle θ.T).restrict (stopping.halt θ.T)ᶜ = 0

namespace AtMostPublicPolicy
variable {B : PublicProblem E θ}

def outputLaw (A : AtMostPublicPolicy B) (I : PrivateInstance B) : Measure B.X :=
  A.stopping.eventualOutputLaw A.base.strategy A.base.seedLaw I.oracle

instance outputLaw_probability (A : AtMostPublicPolicy B) (I : PrivateInstance B) :
    IsProbabilityMeasure (A.outputLaw I) := by
  unfold outputLaw
  rw [A.stopping.eventualOutputLaw_eq_padded A.base.strategy A.base.seedLaw I.oracle (A.call_budget I)]
  infer_instance

def padded (A : AtMostPublicPolicy B) : PublicPolicy B where
  Seed := A.base.Seed
  seedSpace := A.base.seedSpace
  seedLaw := A.base.seedLaw
  seed_probability := A.base.seed_probability
  strategy := A.stopping.paddedPolicy A.base.strategy

theorem padded_outputLaw (A : AtMostPublicPolicy B) (I : PrivateInstance B) :
    PublicPolicy.outputLaw A.padded I = A.outputLaw I :=
  (A.stopping.eventualOutputLaw_eq_padded A.base.strategy A.base.seedLaw I.oracle (A.call_budget I)).symm

def ofFixed (A : PublicPolicy B) : AtMostPublicPolicy B where
  base := A
  stopping := AdaptiveKernel.StoppingRule.terminalHalt A.strategy ⟨B.initial, B.initial_feasible⟩
  call_budget I := AdaptiveKernel.StoppingRule.terminalHalt_budget A.strategy _ A.seedLaw I.oracle

theorem ofFixed_outputLaw (A : PublicPolicy B) (I : PrivateInstance B) :
    (ofFixed A).outputLaw I = PublicPolicy.outputLaw A I :=
  AdaptiveKernel.StoppingRule.terminalHalt_eventualOutputLaw A.strategy _ A.seedLaw I.oracle

end AtMostPublicPolicy

def AtMostPublicAlgorithm (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) := ∀ B : PublicProblem E θ, AtMostPublicPolicy B

def atMostModelOutputLaw (I : ModelInstance E θ) (A : AtMostPublicAlgorithm E θ) : Measure I.1.X :=
  (A I.1).outputLaw I.2

instance atMostModelOutputLaw_probability (I : ModelInstance E θ) (A : AtMostPublicAlgorithm E θ) :
    IsProbabilityMeasure (atMostModelOutputLaw I A) := by
  unfold atMostModelOutputLaw
  infer_instance

def atMostCallMinimax (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) : ℝ≥0∞ :=
  extendedMinimaxQuantile (atMostModelOutputLaw (E := E) (θ := θ)) (fun I _ => I.2.loss) θ.δ

/-- Actual bounded causal stopping and exactly-T execution have the same
minimax quantile. Padding is uniform across all private instances. -/
theorem atMostCallMinimax_eq_fixedCallMinimax (θ : OracleParameters) :
    atMostCallMinimax E θ = fixedCallMinimax E θ := by
  apply le_antisymm
  · apply le_iInf
    intro A
    let A' : AtMostPublicAlgorithm E θ := fun B => AtMostPublicPolicy.ofFixed (A B)
    have he : uniformExtendedThresholds (atMostModelOutputLaw (E := E) (θ := θ))
        (fun (I : ModelInstance E θ) (_ : AtMostPublicAlgorithm E θ) => I.2.loss) θ.δ A' =
        uniformExtendedThresholds (modelOutputLaw (E := E) (θ := θ))
        (fun (I : ModelInstance E θ) (_ : PublicAlgorithm E θ) => I.2.loss) θ.δ A := by
      ext ε
      change (∀ I : ModelInstance E θ, ((AtMostPublicPolicy.ofFixed (A I.1)).outputLaw I.2).real
        {x | ε < I.2.loss x} ≤ θ.δ) ↔
        (∀ I : ModelInstance E θ, (PublicPolicy.outputLaw (A I.1) I.2).real
        {x | ε < I.2.loss x} ≤ θ.δ)
      simp only [AtMostPublicPolicy.ofFixed_outputLaw]
    change atMostCallMinimax E θ ≤ sInf _
    rw [← he]
    exact iInf_le _ A'
  · apply le_iInf
    intro A
    let A' : PublicAlgorithm E θ := fun B => (A B).padded
    have he : uniformExtendedThresholds (modelOutputLaw (E := E) (θ := θ))
        (fun (I : ModelInstance E θ) (_ : PublicAlgorithm E θ) => I.2.loss) θ.δ A' =
        uniformExtendedThresholds (atMostModelOutputLaw (E := E) (θ := θ))
        (fun (I : ModelInstance E θ) (_ : AtMostPublicAlgorithm E θ) => I.2.loss) θ.δ A := by
      ext ε
      change (∀ I : ModelInstance E θ, (PublicPolicy.outputLaw (A I.1).padded I.2).real
        {x | ε < I.2.loss x} ≤ θ.δ) ↔
        (∀ I : ModelInstance E θ, ((A I.1).outputLaw I.2).real
        {x | ε < I.2.loss x} ≤ θ.δ)
      simp only [AtMostPublicPolicy.padded_outputLaw]
    change fixedCallMinimax E θ ≤ sInf _
    rw [← he]
    exact iInf_le _ A'

end HeavyTail
