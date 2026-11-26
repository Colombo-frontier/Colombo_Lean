import Nonsmooth.MeasurableSimulation
import Nonsmooth.Minimax
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A single adversarial parameter is selected after the entire seed law is fixed.
Joint integrability justifies the exchange of the two probability integrals. -/
theorem fixed_parameter_of_prior_risk {Λ Ω : Type*} [MeasurableSpace Λ] [MeasurableSpace Ω]
    {Q : Measure Λ} {P : Measure Ω} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (loss : Λ → Ω → ℝ) (hi : Integrable (Function.uncurry loss) (Q.prod P))
    {ε C : ℝ} (hε : ε < C) (hprior : ∀ᵐ ω ∂P, C ≤ ∫ v, loss v ω ∂Q) :
    ∃ v, ε < ∫ ω, loss v ω ∂P := by
  by_contra hnot
  push_neg at hnot
  have hlo := integral_mono_ae (μ := P) (integrable_const C) hi.integral_prod_right hprior
  have hhi := integral_mono (μ := Q) hi.integral_prod_left (integrable_const ε) hnot
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hlo hhi
  have hswap := integral_integral_swap hi
  change (∫ v, ∫ ω, loss v ω ∂P ∂Q) = ∫ ω, ∫ v, loss v ω ∂Q ∂P at hswap
  change C ≤ ∫ ω, ∫ v, loss v ω ∂Q ∂P at hlo
  change (∫ v, ∫ ω, loss v ω ∂P ∂Q) ≤ ε at hhi
  linarith

theorem family_policy_run_measurable {Λ Ω S X : Type*}
    [MeasurableSpace Λ] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    {p : Policy Ω S X} (hp : p.IsMeasurable) (F : Λ → X → ℝ)
    (hF : Measurable (Function.uncurry F)) (T : ℕ) :
    Measurable (fun z : Λ × Ω => p.run (F z.1) z.2 T) := by
  induction T with
  | zero => exact hp.initial.comp measurable_snd
  | succ n ih =>
    have hq : Measurable (fun z : Λ × Ω => p.query n z.2 (p.run (F z.1) z.2 n)) :=
      (hp.query n).comp (measurable_snd.prodMk ih)
    have hv := hF.comp (measurable_fst.prodMk hq)
    exact (hp.update n).comp (measurable_snd.prodMk (ih.prodMk hv))

theorem family_policy_output_measurable {Λ Ω S X : Type*}
    [MeasurableSpace Λ] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    {p : Policy Ω S X} (hp : p.IsMeasurable) (F : Λ → X → ℝ)
    (hF : Measurable (Function.uncurry F)) (T : ℕ) :
    Measurable (fun z : Λ × Ω => p.result (F z.1) z.2 T) :=
  hp.output.comp (measurable_snd.prodMk (family_policy_run_measurable hp F hF T))

end
end Nonsmooth
