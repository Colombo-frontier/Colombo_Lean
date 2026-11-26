import Bilevel.StatefulProcedure
import Bilevel.MSETransfer
import Mathlib.Probability.Kernel.Composition.Prod

/-! One original oracle call with an arbitrary measurable history-dependent
law. The observation can retain both correlated full-gradient vectors. A
component is read only after the joint observation and history update. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful

namespace KernelMap
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

def dependent (K : Kernel A B) (f : A × B → C) : Kernel A C :=
  (Kernel.id ×ₖ K).map f

instance dependent_markov (K : Kernel A B) [IsMarkovKernel K]
    (f : A × B → C) (hf : Measurable f) : IsMarkovKernel (dependent K f) :=
  Kernel.IsMarkovKernel.map _ hf

theorem dependent_apply (K : Kernel A B) [IsMarkovKernel K]
    (f : A × B → C) (hf : Measurable f) (a : A) :
    dependent K f a = (K a).map (fun b => f (a,b)) := by
  ext s hs
  rw [dependent, Kernel.map_apply _ hf, Measure.map_apply hf hs,
    Kernel.id_prod_apply' _ _ (hf hs),
    Measure.map_apply (show Measurable (fun b => f (a,b)) from
      hf.comp (measurable_const.prodMk measurable_id)) hs]
  rfl
end KernelMap

variable {Query History Obs E : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- A component of one joint original SFO response. No restriction is imposed
on how its conditional law varies with the full entering history. -/
structure HistoryOracle (σ : ℝ) where
  law : Kernel (Query × History) Obs
  markov : IsMarkovKernel law
  read : Obs → E
  read_measurable : Measurable read
  truth : Query → E
  truth_measurable : Measurable truth
  update : (Query × History) × Obs → History
  update_measurable : Measurable update
  square_integrable : ∀ q h, Integrable (fun o => ‖read o - truth q‖ ^ 2) (law (q,h))
  mean : ∀ q h, (∫ o, read o - truth q ∂law (q,h)) = 0
  variance : ∀ q h, (∫ o, ‖read o - truth q‖ ^ 2 ∂law (q,h)) ≤ σ ^ 2

attribute [instance] HistoryOracle.markov

namespace HistoryOracle
variable {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

def finish (z : (Query × History) × Obs) : Outcome E History :=
  (O.read z.2, O.update z, 1)

omit [BorelSpace E] [SecondCountableTopology E] in
theorem finish_measurable : Measurable O.finish :=
  (O.read_measurable.comp measurable_snd).prodMk (O.update_measurable.prodMk measurable_const)

def call : Procedure Query History E where
  law := KernelMap.dependent O.law O.finish
  markov := KernelMap.dependent_markov _ _ O.finish_measurable

omit [BorelSpace E] [SecondCountableTopology E] in
theorem call_law (q : Query) (h : History) :
    O.call.law (q,h) = (O.law (q,h)).map (fun o => (O.read o, O.update ((q,h),o), 1)) :=
  KernelMap.dependent_apply _ _ O.finish_measurable _

theorem error_memLp (q : Query) (h : History) :
    MemLp (fun o => O.read o - O.truth q) 2 (O.law (q,h)) :=
  (memLp_two_iff_integrable_sq_norm (O.read_measurable.sub measurable_const).aestronglyMeasurable).mpr
    (O.square_integrable q h)

theorem error_integrable (q : Query) (h : History) :
    Integrable (fun o => O.read o - O.truth q) (O.law (q,h)) :=
  (O.error_memLp q h).integrable (by norm_num)

omit [SecondCountableTopology E] in
theorem call_mse : O.call.MSEBound O.truth (fun _ => σ) := by
  intro q h
  rw [call_law]
  have hm : Measurable (fun o => (O.read o, O.update ((q,h),o), 1)) :=
    O.finish_measurable.comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun z : Outcome E History => ‖z.1 - O.truth q‖ ^ 2) := by fun_prop
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr
    (O.square_integrable q h), ?_⟩
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact O.variance q h

theorem call_mean : O.call.Mean O.truth := by
  intro q h
  rw [call_law]
  have hm : Measurable (fun o => (O.read o, O.update ((q,h),o), 1)) :=
    O.finish_measurable.comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun z : Outcome E History => z.1 - O.truth q) := by fun_prop
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr
    (O.error_integrable q h), ?_⟩
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact O.mean q h

omit [BorelSpace E] [SecondCountableTopology E] in
theorem call_calls : O.call.CallsEq (fun _ => 1) := by
  intro q h
  rw [call_law]
  have hm : Measurable (fun o => (O.read o, O.update ((q,h),o), 1)) :=
    O.finish_measurable.comp (measurable_const.prodMk measurable_id)
  have hp : MeasurableSet {z : Outcome E History | z.2.2 = 1} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton 1)
  apply (ae_map_iff hm.aemeasurable hp).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

end HistoryOracle
end Bilevel.Stateful
