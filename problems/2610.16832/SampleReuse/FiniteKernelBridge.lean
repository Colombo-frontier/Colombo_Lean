import SampleReuse.PersistentSeededTable
import SampleReuse.PersistentHiddenStage

/-! Exact compatibility of the finite probability-law semantics with the
measurable kernel semantics used in the entropy and stopping bounds. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

def finitePMFKernel {B C : Type} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] (p : B → PMF C) : Kernel B C where
  toFun b := (p b).toMeasure
  measurable' := measurable_of_countable _

instance finitePMFKernel_markov {B C : Type} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] [MeasurableSpace C] (p : B → PMF C) :
    IsMarkovKernel (finitePMFKernel p) where
  isProbabilityMeasure _ := by change IsProbabilityMeasure (p _).toMeasure; infer_instance

theorem finiteConditionalPMF_measure {B C : Type} [Fintype B] [Fintype C]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C] (p : PMF B) (q : B → PMF C) :
    (finiteConditionalPMF p q).toMeasure = p.toMeasure ⊗ₘ finitePMFKernel q := by
  apply Measure.ext_of_singleton
  rintro ⟨b, c⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finiteConditionalPMF_apply]
  have he : ({(b, c)} : Set (B × C)) = {b} ×ˢ {c} := by ext z; simp
  rw [he, Measure.compProd_apply_prod (measurableSet_singleton b) (measurableSet_singleton c),
    lintegral_singleton]
  change p b * q b c = (q b).toMeasure {c} * p.toMeasure {b}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton c),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), mul_comm]

variable {S A Key : Type} [Fintype S] [Fintype A] [Fintype Key]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem finiteAdaptiveLaw_measure (ν : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) :
    ∀ n, (finiteAdaptiveLaw ν K n).toMeasure =
      adaptiveKernelLaw ν.toMeasure (fun n => finitePMFKernel (K n)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (finiteConditionalPMF (finiteAdaptiveLaw ν K n) (K n)).toMeasure = _
    rw [finiteConditionalPMF_measure, ih]
    rfl

/-- The actual hidden-dependent fixed-table law is the corresponding
adaptive measurable cache-kernel law, not merely a matching expectation. -/
theorem seeded_table_kernel_law (ν : PMF S) (query : ∀ n, FiniteHistory S A n → Key)
    (p : S → Key → PMF A) (n : ℕ) :
    (seededTablePMF ν p).toMeasure.map (fun z => tableHistory query z.1 z.2 n) =
      adaptiveKernelLaw ν.toMeasure (fun n => finitePMFKernel (seededDisclosurePMF query p n)) n := by
  rw [PMF.toMeasure_map _ _ (measurable_of_countable _), seeded_table_history_law,
    finiteAdaptiveLaw_measure]

end
end SampleReuse
