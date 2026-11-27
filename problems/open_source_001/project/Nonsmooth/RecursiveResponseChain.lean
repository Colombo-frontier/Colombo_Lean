import Nonsmooth.RecursiveBeliefDisintegration
import Nonsmooth.KernelInvariantConsequences

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

def recursiveResponseKernel (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Kernel (ResponseHistory k n) (Fin k × ℝ) :=
  (observedKernel (recursiveSupportBelief Q u hu n)
    (fun p => supportSingleObservation (u n p.1) p.2)
    (supportParametricObservation_measurable (u n) (hu n))).fst

instance recursiveResponseKernel_markov (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    IsMarkovKernel (recursiveResponseKernel Q u hu n) := by
  unfold recursiveResponseKernel
  infer_instance

theorem recursiveResponseKernel_apply (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (h : ResponseHistory k n) :
    recursiveResponseKernel Q u hu n h =
      (recursiveSupportBelief Q u hu n h).map (supportSingleObservation (u n h)) :=
  observedKernel_fst _ _ _ h

def recursiveResponseStep (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Kernel (ResponseHistory k n) (ResponseHistory k (n + 1)) :=
  (Kernel.id ×ₖ recursiveResponseKernel Q u hu n).map responseHistoryJoin

instance recursiveResponseStep_markov (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    IsMarkovKernel (recursiveResponseStep Q u hu n) :=
  Kernel.IsMarkovKernel.map _ responseHistoryJoin_measurable

theorem recursiveResponseStep_apply (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (h : ResponseHistory k n) :
    recursiveResponseStep Q u hu n h =
      (recursiveResponseKernel Q u hu n h).map (fun y => responseHistoryJoin (h, y)) := by
  have hj : Measurable (fun y : Fin k × ℝ => responseHistoryJoin (h, y)) :=
    responseHistoryJoin_measurable.comp measurable_prodMk_left
  ext S hS
  rw [recursiveResponseStep, Kernel.map_apply' _ responseHistoryJoin_measurable h hS,
    Kernel.id_prod_apply' _ _ (responseHistoryJoin_measurable hS),
    Measure.map_apply hj hS]
  rfl

theorem recursiveResponseStep_mix (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ)
    (ν : Measure (ResponseHistory k n)) [IsFiniteMeasure ν] :
    ν.bind (recursiveResponseStep Q u hu n) =
      (ν ⊗ₘ recursiveResponseKernel Q u hu n).map responseHistoryJoin := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _),
    Measure.map_apply responseHistoryJoin_measurable hS,
    Measure.compProd_apply (responseHistoryJoin_measurable hS)]
  apply lintegral_congr
  intro h
  have hj : Measurable (fun y : Fin k × ℝ => responseHistoryJoin (h, y)) :=
    responseHistoryJoin_measurable.comp measurable_prodMk_left
  rw [recursiveResponseStep_apply,
    Measure.map_apply hj hS]
  rfl

/-- The finite kernel chain has exactly the law of the actual recursively
observed responses under the original prior. -/
theorem recursiveResponseChain_law (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n))
    (h₀ : ResponseHistory k 0) (n : ℕ) :
    kernelChain (recursiveResponseStep Q u hu) n h₀ = Q.map (recursiveSupportResponse u n) := by
  induction n with
  | zero =>
    change Measure.dirac h₀ = Q.map (fun _ : Fin k → E => (Fin.elim0 : ResponseHistory k 0))
    simp only [Measure.map_const, measure_univ, one_smul]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    change (kernelChain (recursiveResponseStep Q u hu) n h₀).bind
      (recursiveResponseStep Q u hu n) = _
    rw [ih, recursiveResponseStep_mix]
    let X := recursiveSupportResponse u n
    let F : ResponseHistory k n × (Fin k → E) → Fin k × ℝ :=
      fun p => supportSingleObservation (u n p.1) p.2
    have hX : Measurable X := recursiveSupportResponse_measurable u hu n
    have hF : Measurable F := supportParametricObservation_measurable (u n) (hu n)
    have hW : Measurable (fun a : Fin k → E => (X a, F (X a, a))) :=
      hX.prodMk (hF.comp (hX.prodMk measurable_id))
    have hbase := observedPosterior_update_base Q X hX id measurable_id
      (recursiveSupportBelief Q u hu n) (recursiveSupportBelief_disintegrates Q u hu n) F hF
    change Q.map (fun a => (X a, F (X a, a))) =
      (Q.map (recursiveSupportResponse u n)) ⊗ₘ recursiveResponseKernel Q u hu n at hbase
    rw [← hbase, Measure.map_map responseHistoryJoin_measurable hW]
    rfl

end
end Nonsmooth
