import SampleReuse.PersistentHiddenTable
import SecondOrder.KernelStoppedHit

/-! Coupling the uncapped reusable-table execution to its capped information
experiment. Activation before the quota transfers without paying the
probability that the quota itself is exhausted. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {S A : Type} [MeasurableSpace S] [MeasurableSpace A]

def quotaSafe (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ)
    (E : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) : Set (FiniteHistory S A n) :=
  {h | kernelChargeCount selected cap n h < cap} ∩ (E n)ᶜ

def quotaHit (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ)
    (E : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) : Set (FiniteHistory S A n) :=
  {h | kernelChargeCount selected cap n h < cap} ∩ E n

theorem quotaSafe_measurable (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ)
    (E : ∀ n, Set (FiniteHistory S A n)) (hE : ∀ n, MeasurableSet (E n)) (n : ℕ) :
    MeasurableSet (quotaSafe selected cap E n) :=
  (measurableSet_lt (kernelChargeCount_measurable selected hs cap n) measurable_const).inter (hE n).compl

theorem quotaHit_measurable (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ)
    (E : ∀ n, Set (FiniteHistory S A n)) (hE : ∀ n, MeasurableSet (E n)) (n : ℕ) :
    MeasurableSet (quotaHit selected cap E n) :=
  (measurableSet_lt (kernelChargeCount_measurable selected hs cap n) measurable_const).inter (hE n)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem quotaHit_disjoint (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ)
    (E : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) :
    Disjoint (quotaHit selected cap E n) (quotaSafe selected cap E n) := by
  exact Set.disjoint_left.mpr (fun _ hh hs => hs.2 hh.2)

/-- This is an equality-before-stopping argument for actual kernel laws,
not an independent-samples argument for repeated queries. -/
theorem uncapped_quota_hit_le_capped_activation
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (dummy n)]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (E : ∀ n, Set (FiniteHistory S A n)) (hE : ∀ n, MeasurableSet (E n)) (N : ℕ) :
    (adaptiveKernelLaw μ K N).real
      (kernelStoppedHitSet (quotaSafe selected cap E) (quotaHit selected cap E) N) ≤
      (adaptiveKernelLaw μ (cappedResponseKernel selected hs cap K dummy) N).real
        (kernelSurvivalSet (fun n => (E n)ᶜ) N)ᶜ := by
  have heq (n : ℕ) (h : FiniteHistory S A n) (hh : h ∈ quotaSafe selected cap E n) :
      K n h = cappedResponseKernel selected hs cap K dummy n h := by
    have hc : kernelChargeCount selected cap n h < cap := hh.1
    simp only [cappedResponseKernel, Kernel.piecewise_apply, Set.mem_setOf_eq, if_pos hc]
  rw [kernelStoppedHit_probability_eq μ K (cappedResponseKernel selected hs cap K dummy)
    (quotaSafe selected cap E) (quotaHit selected cap E)
    (quotaSafe_measurable selected hs cap E hE) (quotaHit_measurable selected hs cap E hE)
    (quotaHit_disjoint selected cap E) heq N]
  apply measureReal_mono
  · apply (kernelStoppedHitSet_subset_ever _ _ N).trans
    apply Set.compl_subset_compl.mpr
    apply kernelSurvivalSet_mono
    intro n h hh he
    exact hh he.2
  · finiteness

end
end SampleReuse
