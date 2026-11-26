import RandomizedFO2003.ActionProgram
import RandomizedFO2003.FrameMeasurability

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Measurability of the actual finite transcript under any jointly
measurable operator and initial history, including degenerate operators. -/
theorem ActionProgram.run_family_measurable (n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (operator : Ω → E →L[ℝ] E) (hoperator : Measurable operator)
    (history : Ω → H) (hhistory : Measurable history) :
    Measurable (fun ω => plan.run n (operator ω) (history ω)) := by
  induction n generalizing H with
  | zero => exact hhistory
  | succ n ih =>
    have hx := plan.1.measurable_vector.comp hhistory
    have hr : Measurable (fun ω => plan.1.kind.action (operator ω) (plan.1.vector (history ω))) := by
      cases hk : plan.1.kind
      case query => exact measurable_operator_apply (measurable_operator_adjoint hoperator) hx
      case response => exact measurable_operator_apply hoperator hx
    exact ih plan.2 (fun ω => (history ω, plan.1.kind.action (operator ω) (plan.1.vector (history ω))))
      (hhistory.prodMk hr)

end RandomizedFO2003.Rotations
