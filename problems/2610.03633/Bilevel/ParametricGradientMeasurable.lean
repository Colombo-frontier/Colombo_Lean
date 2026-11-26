import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Bilevel.ChiPrefixReadout

/-! Joint measurability of the canonical gradient of a continuous scalar
family in finite-dimensional query variables, including arbitrary finite
disclosed-column arrays and a discrete varying prefix. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ParametricGradient

variable {P E : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem gradient_measurable (f : P → E → ℝ) (hf : Continuous (Function.uncurry f)) :
    Measurable (fun p : P × E => gradient (f p.1) p.2) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv_with_param ℝ hf)

theorem disclosed_gradient_measurable (n r : ℕ) (R : ℝ) (f : ChiBoundedChain.Space n → ℝ)
    (hf : Continuous f) :
    Measurable (fun p : (Fin (n+1) → E) × E =>
      gradient (ChiPrefixEvaluation.disclosedEvaluator n r R p.1 f) p.2) :=
  gradient_measurable (P := Fin (n+1) → E) (E := E)
    (fun columns => ChiPrefixEvaluation.disclosedEvaluator n r R columns f)
    (ChiPrefixEvaluation.disclosedEvaluator_continuous n r R f hf)

theorem disclosed_gradient_varying_prefix_measurable (n : ℕ) (R : ℝ)
    (f : ChiBoundedChain.Space n → ℝ) (hf : Continuous f) :
    Measurable (fun p : ((Fin (n+1) → E) × E) × ℕ =>
      gradient (ChiPrefixEvaluation.disclosedEvaluator n p.2 R p.1.1 f) p.1.2) :=
  measurable_from_prod_countable (fun r => disclosed_gradient_measurable n r R f hf)

end Bilevel.ParametricGradient
