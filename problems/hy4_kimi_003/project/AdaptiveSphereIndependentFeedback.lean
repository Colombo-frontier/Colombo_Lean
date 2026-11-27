import Mathlib.Probability.Independence.Conditional

/-! The manuscript's information-independent feedback clause, at the level of
the entire genuine regular conditional distribution, not only its mean. -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Task006.AdaptiveSphereKernel
noncomputable section

/-- Revealing feedback conditionally independent of the hidden parameter,
given the current past, leaves its whole regular conditional law unchanged. -/
theorem independent_feedback_preserves_condDistrib
    {W H V B : Type*} [mW : MeasurableSpace W] [StandardBorelSpace W]
    [MeasurableSpace H] [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (μ : Measure W) [IsProbabilityMeasure μ]
    (past : W → H) (hpast : Measurable past) (θ : W → V) (hθ : Measurable θ)
    (feedback : W → B) (hfeedback : Measurable feedback)
    (hind : feedback ⟂ᵢ[past,hpast;μ] θ) :
    condDistrib θ (fun w => (past w,feedback w)) μ
      =ᵐ[μ.map (fun w => (past w,feedback w))]
      (condDistrib θ past μ).prodMkRight B := by
  exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hθ hfeedback hpast).mp hind

#print axioms independent_feedback_preserves_condDistrib
end
end Task006.AdaptiveSphereKernel
