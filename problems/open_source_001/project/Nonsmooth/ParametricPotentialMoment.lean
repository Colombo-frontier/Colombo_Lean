import Nonsmooth.PotentialMomentDerivative

open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def potentialWeightedIntegral (V F : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, F t x * Real.exp (-V t x)

/-- Explicit local hypotheses for differentiating a potential-weighted moment.
The dominating function bounds the actual differentiated integrand. -/
def PotentialMomentRegularAt (V s F F' : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ → ℝ,
    (∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun x => F r x * Real.exp (-V r x))) ∧
    Integrable (fun x => F t x * Real.exp (-V t x)) ∧
    AEStronglyMeasurable (fun x => (F' t x - F t x * s t x) * Real.exp (-V t x)) ∧
    Integrable B ∧
    ∀ᵐ x ∂(volume : Measure ℝ), ∀ r ∈ Metric.ball t ε,
      HasDerivAt (fun r => V r x) (s r x) r ∧
      HasDerivAt (fun r => F r x) (F' r x) r ∧
      ‖(F' r x - F r x * s r x) * Real.exp (-V r x)‖ ≤ B x

theorem potentialWeightedIntegral_derivative (V s F F' : ℝ → ℝ → ℝ) (t : ℝ)
    (hreg : PotentialMomentRegularAt V s F F' t) :
    Integrable (fun x => (F' t x - F t x * s t x) * Real.exp (-V t x)) ∧
      HasDerivAt (potentialWeightedIntegral V F)
        (∫ x, (F' t x - F t x * s t x) * Real.exp (-V t x)) t := by
  obtain ⟨ε, hε, B, hmeas, hi, hDmeas, hB, hlocal⟩ := hreg
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), ∀ r ∈ Metric.ball t ε,
      ‖(F' r x - F r x * s r x) * Real.exp (-V r x)‖ ≤ B x := by
    filter_upwards [hlocal] with x hx
    exact fun r hr => (hx r hr).2.2
  have hder : ∀ᵐ x ∂(volume : Measure ℝ), ∀ r ∈ Metric.ball t ε,
      HasDerivAt (fun r => F r x * Real.exp (-V r x))
        ((F' r x - F r x * s r x) * Real.exp (-V r x)) r := by
    filter_upwards [hlocal] with x hx
    intro r hr
    convert! (hx r hr).2.1.mul (hx r hr).1.neg.exp using 1 <;>
      (try simp only [Pi.neg_apply]) <;> ring
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x => F r x * Real.exp (-V r x))
    (F' := fun r x => (F' r x - F r x * s r x) * Real.exp (-V r x))
    (Metric.ball_mem_nhds t hε) hmeas hi hDmeas hbound hB hder

end
end Nonsmooth
