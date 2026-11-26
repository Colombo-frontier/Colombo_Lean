import Nonsmooth.SupportPosteriorKernel
import Nonsmooth.ConditionedProducts

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem finite_product_conditioning_rows {α : Type} [MeasurableSpace α] {k : ℕ}
    (μ : Fin k → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (B : Fin k → Set α) (hB : ∀ i, MeasurableSet (B i)) (hpos : ∀ i, μ i (B i) ≠ 0) :
    Measure.pi (fun i => (μ i)[|B i]) = (Measure.pi μ)[|Set.univ.pi B] := by
  letI (i : Fin k) : IsProbabilityMeasure ((μ i)[|B i]) := cond_isProbabilityMeasure (hpos i)
  apply Measure.pi_eq
  intro s hs
  rw [cond_apply (MeasurableSet.univ_pi hB), Measure.pi_pi]
  have he : (Set.univ.pi B) ∩ Set.univ.pi s = Set.univ.pi (fun i => B i ∩ s i) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [he, Measure.pi_pi]
  simp_rw [cond_apply (hB _) (μ _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (hpos i))

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem supportPosteriorKernel_at_atom (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) (h : SupportHistory E k n)
    (hatom : Q.map (fun a => supportAugmentedTranscript p a ω n) {h} ≠ 0) :
    supportPosteriorKernel Q p ω n h = Q[|{a | supportAugmentedTranscript p a ω n = h}] := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
  have hset : MeasurableSet {a : Fin k → E | supportAugmentedTranscript p a ω n = h} :=
    hF (measurableSet_singleton h)
  ext s hs
  rw [supportPosteriorKernel, condDistrib_apply_of_ne_zero measurable_id h hatom,
    cond_apply hset, Measure.map_apply hF (measurableSet_singleton h),
    Measure.map_apply (hF.prodMk measurable_id) ((measurableSet_singleton h).prod hs)]
  rfl

theorem support_consistent_history_product_fiber (p : Policy Ω S E) (ω : Ω) (n : ℕ)
    (h : SupportHistory E k n) (hc : supportHistoryConsistent p ω n h) :
    {a : Fin k → E | supportAugmentedTranscript p a ω n = h} = Set.univ.pi (supportHistoryCell n h) := by
  ext a
  simp only [Set.mem_setOf_eq, supportAugmentedTranscript_fiber, hc, true_and,
    Set.mem_pi, Set.mem_univ, forall_const]

/-- Product posterior factorization for a positive-probability transcript atom.
The nonzero-mass assumption is essential; this does not identify null winner slices. -/
theorem supportPosteriorKernel_at_atom_product (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) (h : SupportHistory E k n)
    (hc : supportHistoryConsistent p ω n h)
    (hatom : (Measure.pi μ).map (fun a => supportAugmentedTranscript p a ω n) {h} ≠ 0) :
    supportPosteriorKernel (Measure.pi μ) p ω n h =
      Measure.pi (fun i => (μ i)[|supportHistoryCell n h i]) := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
  have hpre : (fun a : Fin k → E => supportAugmentedTranscript p a ω n) ⁻¹' {h} =
      Set.univ.pi (supportHistoryCell n h) := support_consistent_history_product_fiber p ω n h hc
  rw [Measure.map_apply hF (measurableSet_singleton h), hpre, Measure.pi_pi] at hatom
  have hpos : ∀ i : Fin k, μ i (supportHistoryCell n h i) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hatom) i (Finset.mem_univ i)
  rw [supportPosteriorKernel_at_atom _ p hp ω n h]
  · rw [support_consistent_history_product_fiber p ω n h hc]
    exact (finite_product_conditioning_rows μ _ (fun i => supportHistoryCell_measurable n h i) hpos).symm
  · rwa [Measure.map_apply hF (measurableSet_singleton h), hpre, Measure.pi_pi]

end
end Nonsmooth
