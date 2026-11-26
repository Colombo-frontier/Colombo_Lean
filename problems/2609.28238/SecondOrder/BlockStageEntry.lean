import SecondOrder.BlockTargetKernel

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- Before first entry, progress is strictly below the target's response
index; conversely that inequality excludes all earlier entries. -/
theorem blockBeforeEntry_iff (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (hj : 0<j.val) :
    ∀ n h, h ∈ kernelBeforeSet (blockPreEntrySet active query Θ j) n ↔
      blockComparisonProgress active query Θ n h<j.val := by
  intro n
  induction n with
  | zero => intro h; simp only [kernelBeforeSet,Set.mem_univ,blockComparisonProgress,hj]
  | succ n ih =>
    intro h
    change h.1 ∈ kernelSurvivalSet (blockPreEntrySet active query Θ j) n ↔ _
    rw [kernelSurvivalSet_eq_inter_before]
    simp only [Set.mem_inter_iff,blockPreEntrySet,Set.mem_setOf_eq,ih,blockComparisonProgress_succ,max_lt_iff]
    tauto

/-- Positive stages enter exactly at the first query with response index
`j`; the previous historical progress is `j-1`. No reply has yet been drawn. -/
theorem blockFirstEntry_index (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (hj : 0<j.val)
    (n : ℕ) (h : FiniteHistory S A n)
    (he : h ∈ kernelFirstExitSet (blockPreEntrySet active query Θ j) n) :
    blockComparisonIndex active query Θ n h=j.val ∧ blockComparisonProgress active query Θ n h+1=j.val := by
  have hp := (blockBeforeEntry_iff active query Θ j hj n h).mp he.1
  have hn : ¬ blockComparisonIndex active query Θ n h<j.val := fun hi => he.2 ⟨hp,hi⟩
  have hi := (blockComparisonIndex_le active query Θ n h).2
  omega

theorem blockComparisonProgress_update_lt (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (θ : H)
    (n : ℕ) (h : FiniteHistory S A n) :
    blockComparisonProgress active query (Function.update Θ j θ) n h<j.val ↔
      blockComparisonProgress active query Θ n h<j.val := by
  have hp : ∀ i : Fin T, i.val<j.val → Function.update Θ j θ i=Θ i := by
    intro i hi
    exact Function.update_of_ne (by intro he; subst i; omega) _ _
  constructor
  · intro hlt
    have he := blockComparisonProgress_prefix active query (Function.update Θ j θ) Θ n h
      (fun i hi => hp i (by omega))
    rwa [←he]
  · intro hlt
    have he := blockComparisonProgress_prefix active query Θ (Function.update Θ j θ) n h
      (fun i hi => (hp i (by omega)).symm)
    rwa [←he]

/-- The actual comparison experiment has a fresh hidden prior at its
random first entry. The kernel agreement is proved from prefix dependence. -/
theorem blockTarget_firstEntry_independent (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    ((adaptiveKernelLaw (ρ.prod μ) (blockTargetKernel active ha query hq O Θ j) n).restrict
      (finiteHistoryMapInitial Prod.snd n ⁻¹' kernelFirstExitSet (blockPreEntrySet active query Θ j) n)).map
      (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) =
      ρ.prod ((adaptiveKernelLaw μ (blockFixedKernel active ha query hq O Θ) n).restrict
        (kernelFirstExitSet (blockPreEntrySet active query Θ j) n)) :=
  adaptiveKernelLaw_firstEntry_independent ρ μ _ _ (blockPreEntrySet active query Θ j)
    (blockPreEntrySet_measurable active ha query hq Θ j)
    (blockTargetKernel_preEntry_eq active ha query hq O hO Θ j) n

end
end SecondOrder
