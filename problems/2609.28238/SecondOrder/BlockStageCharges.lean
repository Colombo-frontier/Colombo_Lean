import SecondOrder.BlockStageEntry

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- Charge the response only to its own target and only before that target
has been completed in the comparison. -/
def blockChargeStep (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A n) (i : Fin T) : ℕ :=
  if blockComparisonIndex active query Θ n h=i.val ∧ blockComparisonProgress active query Θ n h ≤ i.val then 1 else 0

def blockStageCharges (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) :
    (n : ℕ) → FiniteHistory S A n → Fin T → ℕ
  | 0, _, _ => 0
  | n+1, h, i => blockStageCharges active query Θ n h.1 i+blockChargeStep active query Θ n h.1 i

theorem sum_blockChargeStep_le_one (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H)
    (n : ℕ) (h : FiniteHistory S A n) : ∑ i, blockChargeStep active query Θ n h i≤1 := by
  change (∑ i : Fin T, if blockComparisonIndex active query Θ n h=i.val ∧
    blockComparisonProgress active query Θ n h ≤ i.val then (1:ℕ) else 0)≤1
  rw [←Finset.card_filter]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2.1
  have hj' := (Finset.mem_filter.mp hj).2.1
  exact Fin.ext (hi'.symm.trans hj')

/-- Every actual reply is charged at most once, independently of the
hidden instance, the reply values and the algorithm's adaptivity. -/
theorem sum_blockStageCharges_le (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) :
    ∀ n h, (∑ i, blockStageCharges active query Θ n h i)≤n := by
  intro n
  induction n with
  | zero => intro h; simp only [blockStageCharges,Finset.sum_const_zero,le_refl]
  | succ n ih =>
    intro h
    simp only [blockStageCharges,Finset.sum_add_distrib]
    exact add_le_add (ih h.1) (sum_blockChargeStep_le_one active query Θ n h.1)

theorem blockStageCharges_zero_before_entry (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) :
    ∀ n h, h ∈ kernelBeforeSet (blockPreEntrySet active query Θ j) n →
      blockStageCharges active query Θ n h j=0 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro h hh
    have hp : h.1 ∈ kernelSurvivalSet (blockPreEntrySet active query Θ j) n := hh
    rw [kernelSurvivalSet_eq_inter_before] at hp
    have hindex : blockComparisonIndex active query Θ n h.1<j.val := hp.1.2
    change blockStageCharges active query Θ n h.1 j+blockChargeStep active query Θ n h.1 j=0
    rw [ih h.1 hp.2]
    simp only [blockChargeStep,show ¬blockComparisonIndex active query Θ n h.1=j.val from by omega,
      false_and,if_false,zero_add]

theorem blockChargeStep_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (n : ℕ) (i : Fin T) :
    Measurable (fun z : (Fin T → H) × FiniteHistory S A n => blockChargeStep active query z.1 n z.2 i) :=
  Measurable.ite (((blockComparisonIndex_measurable active ha query hq n) (measurableSet_singleton i.val)).inter
    (measurableSet_le (blockComparisonProgress_measurable active ha query hq n) measurable_const))
    measurable_const measurable_const

theorem blockStageCharges_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (i : Fin T) :
    ∀ n, Measurable (fun z : (Fin T → H) × FiniteHistory S A n => blockStageCharges active query z.1 n z.2 i) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun z : (Fin T → H) × (FiniteHistory S A n × A) =>
      blockStageCharges active query z.1 n z.2.1 i+blockChargeStep active query z.1 n z.2.1 i)
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).add
      ((blockChargeStep_measurable active ha query hq n i).comp (measurable_fst.prodMk measurable_snd.fst))

end
end SecondOrder
