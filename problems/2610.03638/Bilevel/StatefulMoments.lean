import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
import Bilevel.MSETransfer

/-! Moment transport through an actual history-dependent Markov kernel.
No representation by independent samples with a stationary query law is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.StatefulMoments
variable {State Out E : Type*} [MeasurableSpace State] [MeasurableSpace Out]
  {π : Measure State} [IsProbabilityMeasure π]
  (K : Kernel State Out) [IsMarkovKernel K]

theorem fst_preserves : MeasurePreserving (Prod.fst : State×Out → State) (π ⊗ₘ K) π :=
  ⟨measurable_fst,Measure.fst_compProd π K⟩

/-- Conditional integral bounds integrate against every entering history law.
The conclusion includes actual integrability of the full composition. -/
theorem nonnegative_integral_bound (f : State×Out → ℝ) (hf : Measurable f)
    (hn : ∀ z, 0≤f z) (b : State → ℝ) (hb : Integrable b π)
    (hi : ∀ s, Integrable (fun o => f (s,o)) (K s))
    (hbound : ∀ s, (∫ o, f (s,o) ∂K s)≤b s) :
    Integrable f (π ⊗ₘ K) ∧ (∫ z, f z ∂π ⊗ₘ K)≤∫ s,b s ∂π := by
  have hm : StronglyMeasurable (fun s => ∫ o, ‖f (s,o)‖ ∂K s) :=
    hf.stronglyMeasurable.norm.integral_kernel_prod_right'
  have he (s : State) : (∫ o, ‖f (s,o)‖ ∂K s)=(∫ o,f (s,o) ∂K s) := by
    apply integral_congr_ae
    filter_upwards with o
    exact Real.norm_of_nonneg (hn (s,o))
  have hb' : Integrable (fun s => ∫ o, ‖f (s,o)‖ ∂K s) π := by
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_of_nonneg (integral_nonneg (fun o => norm_nonneg _)),he]
    exact hbound s
  have hfull : Integrable f (π ⊗ₘ K) :=
    (Measure.integrable_compProd_iff hf.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hi,hb'⟩
  refine ⟨hfull,?_⟩
  rw [Measure.integral_compProd hfull]
  have hslice : Integrable (fun s => ∫ o,f (s,o) ∂K s) π := by
    simpa only [he] using hb'
  exact integral_mono hslice hb hbound

variable [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
theorem square_integrable_bound (error : State×Out → E) (hm : Measurable error)
    (b : State → ℝ) (hb : Integrable b π)
    (hi : ∀ s, Integrable (fun o => ‖error (s,o)‖^2) (K s))
    (hbound : ∀ s, (∫ o, ‖error (s,o)‖^2 ∂K s)≤b s) :
    Integrable (fun z => ‖error z‖^2) (π ⊗ₘ K) ∧
      (∫ z, ‖error z‖^2 ∂π ⊗ₘ K)≤∫ s,b s ∂π :=
  nonnegative_integral_bound K _ (hm.norm.pow_const 2) (fun _ => sq_nonneg _)
    b hb hi hbound

theorem error_memLp (error : State×Out → E) (hm : Measurable error) (δ : ℝ)
    (hi : ∀ s, Integrable (fun o => ‖error (s,o)‖^2) (K s))
    (hbound : ∀ s, (∫ o, ‖error (s,o)‖^2 ∂K s)≤δ^2) :
    MemLp error 2 (π ⊗ₘ K) :=
  (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    (square_integrable_bound K error hm (fun _ => δ^2) (integrable_const _) hi hbound).1

omit [SecondCountableTopology E] in
theorem error_mse (error : State×Out → E) (hm : Measurable error) (δ : ℝ)
    (hi : ∀ s, Integrable (fun o => ‖error (s,o)‖^2) (K s))
    (hbound : ∀ s, (∫ o, ‖error (s,o)‖^2 ∂K s)≤δ^2) :
    (∫ z, ‖error z‖^2 ∂π ⊗ₘ K)≤δ^2 := by
  simpa using (square_integrable_bound (π := π) K error hm (fun _ => δ^2) (integrable_const _) hi hbound).2

end Bilevel.StatefulMoments
