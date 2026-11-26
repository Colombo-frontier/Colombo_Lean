import SecondOrder.BlockStageEntry
import SecondOrder.KernelEntryTail

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- Activation of the target before the comparison may inspect it. Other
hidden blocks are fixed but arbitrary; the private initial state is random. -/
def blockTargetFarEvent (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    Set (FiniteHistory (H × S) A n) :=
  {h | blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial n h).1)
      n (finiteHistoryMapInitial Prod.snd n h)<j.val ∧
    active j (finiteHistoryInitial n h).1 (query n (finiteHistoryMapInitial Prod.snd n h))}

theorem blockTargetFarEvent_public (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    blockTargetFarEvent active query Θ j n =
      {h | blockComparisonProgress active query Θ n (finiteHistoryMapInitial Prod.snd n h)<j.val ∧
        active j (finiteHistoryInitial n h).1 (query n (finiteHistoryMapInitial Prod.snd n h))} := by
  ext h
  exact and_congr (blockComparisonProgress_update_lt active query Θ j _ n _) Iff.rfl

theorem blockTargetFarEvent_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : MeasurableSet (blockTargetFarEvent active query Θ j n) := by
  rw [blockTargetFarEvent_public]
  exact (measurableSet_lt
    (((blockComparisonProgress_measurable active ha query hq n).comp measurable_prodMk_left).comp
      (finiteHistoryMapInitial_measurable measurable_snd n)) measurable_const).inter
    ((ha j).preimage ((measurable_fst.comp (finiteHistoryInitial_measurable n)).prodMk
      ((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n))))

/-- The far-jump bound is derived for the actual comparison law. It does
not assume independence after conditioning on nonactivation of the target. -/
theorem blockTarget_far_probability (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) {q : ℝ≥0∞}
    (htail : ∀ x, ρ {θ | active j θ x}≤q) :
    adaptiveKernelLaw (ρ.prod μ) (blockTargetKernel active ha query hq O Θ j) n
      (blockTargetFarEvent active query Θ j n) ≤ q := by
  by_cases hj : j.val=0
  · have he : blockTargetFarEvent active query Θ j n=∅ := by
      ext h
      simp only [blockTargetFarEvent,hj,Nat.not_lt_zero,false_and,Set.mem_setOf_eq,Set.mem_empty_iff_false]
    rw [he,measure_empty]
    exact zero_le _
  · have hj' : 0<j.val := by omega
    let F : Set (H × FiniteHistory S A n) := {z | active j z.1 (query n z.2)}
    have hF : MeasurableSet F := (ha j).preimage (measurable_fst.prodMk ((hq n).comp measurable_snd))
    have hb := kernelBeforeSet_measurable (blockPreEntrySet active query Θ j)
      (blockPreEntrySet_measurable active ha query hq Θ j) n
    have ht := adaptiveKernelLaw_entry_tail ρ μ
      (blockTargetKernel active ha query hq O Θ j) (blockFixedKernel active ha query hq O Θ)
      (blockPreEntrySet active query Θ j) (blockPreEntrySet_measurable active ha query hq Θ j)
      (blockTargetKernel_preEntry_eq active ha query hq O hO Θ j) n hb Set.Subset.rfl hF
      (fun h => htail (query n h))
    have he : blockTargetFarEvent active query Θ j n =
        {h | ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ F ∧
          finiteHistoryMapInitial Prod.snd n h ∈ kernelBeforeSet (blockPreEntrySet active query Θ j) n} := by
      rw [blockTargetFarEvent_public]
      ext h
      simp only [Set.mem_setOf_eq,F,blockBeforeEntry_iff active query Θ j hj',and_comm]
    rw [he]
    apply ht.trans
    calc
      _ ≤ q*1 := mul_le_mul_left' ((measure_mono (Set.subset_univ _)).trans_eq (measure_univ)) q
      _ = q := mul_one q

theorem blockTarget_far_probability_real (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) {q : ℝ} (hq₀ : 0≤q)
    (htail : ∀ x, ρ.real {θ | active j θ x}≤q) :
    (adaptiveKernelLaw (ρ.prod μ) (blockTargetKernel active ha query hq O Θ j) n).real
      (blockTargetFarEvent active query Θ j n) ≤ q := by
  apply ENNReal.toReal_le_of_le_ofReal hq₀
  apply blockTarget_far_probability ρ μ active ha query hq O hO Θ j n
  intro x
  rw [←ENNReal.ofReal_toReal (measure_ne_top ρ {θ | active j θ x})]
  exact ENNReal.ofReal_le_ofReal (htail x)

end
end SecondOrder
