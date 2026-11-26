import Smoothness2601.IndependentExecution
import Smoothness2601.SineOracle

/-! Concrete execution law of the article's exact-f/fresh-Bernoulli-g oracle. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry Bilevel.IndependentDraws
namespace Smoothness2601.FreshBernoulli

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  (A : Adaptive.Algorithm X Y)
  (signal : Adaptive.Query X Y → Joint X Y) (hsignal : Measurable signal)
  {B : ℝ} (hB : 0 < B) (hsmall : B ≤ b.σ) (henv : ∀ q, ‖signal q‖ ≤ B)

theorem oracle_output_law (N : ℕ) (input : X × Y) :
    Adaptive.outputKernel A (oracle P signal hsignal hB hsmall henv) N () input =
      ((A.initialLaw input).prod
        (Bilevel.IndependentDraws.law (BernoulliOracle.law (BernoulliOracle.revealProbability B b.σ)
          (BernoulliOracle.revealProbability_le_one hB.le b.σ_pos hsmall)) N)).map
        (fun z => A.output (IndependentExecution.memoryRun A
          (sample P signal (BernoulliOracle.revealProbability B b.σ)) z.1 N z.2)) := by
  apply IndependentExecution.output_law A _ (sample_measurable P signal hsignal _) _ _
  intro q
  exact law_apply P signal hsignal _ _ q ()

end Smoothness2601.FreshBernoulli
