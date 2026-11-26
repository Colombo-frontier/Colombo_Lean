import SecondOrder.BlockStageAgreement
import SecondOrder.HistoryRebase

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockRebasedInactive (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (j : Fin T) (θ : H) (n k : ℕ) :
    Set (FiniteHistory (FiniteHistory S A n) A k) :=
  {h | ¬active j θ (rebasedQuery query n k h)}

theorem blockRebasedInactive_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (j : Fin T) (θ : H) (n k : ℕ) : MeasurableSet (blockRebasedInactive active query j θ n k) :=
  ((ha j).preimage (measurable_const.prodMk (rebasedQuery_measurable query hq n k))).compl

/-- Until the first target activation, actual historical progress remains
in the target stage and every selected capped-stage reply is charged in
the original comparison history. The original entry count need not be zero. -/
theorem blockRebased_before_invariants (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (θ : H)
    (n cap : ℕ) : ∀ k (h : FiniteHistory (FiniteHistory S A n) A k),
    j.val≤blockComparisonProgress active query (Function.update Θ j θ) n (finiteHistoryInitial k h)+1 →
    blockComparisonProgress active query (Function.update Θ j θ) n (finiteHistoryInitial k h)≤j.val →
    h ∈ kernelBeforeSet (blockRebasedInactive active query j θ n) k →
    j.val≤blockComparisonProgress active query (Function.update Θ j θ) (n+k) (historyRebase n k h)+1 ∧
    blockComparisonProgress active query (Function.update Θ j θ) (n+k) (historyRebase n k h)≤j.val ∧
    kernelChargeCount (blockStageSelected active (rebasedQuery query n) Θ j) cap k h≤
      blockStageCharges active query (Function.update Θ j θ) (n+k) (historyRebase n k h) j := by
  intro k
  induction k with
  | zero => intro h hl hu _; exact ⟨hl,hu,Nat.zero_le _⟩
  | succ k ih =>
    intro h hl hu hb
    have hp : h.1 ∈ kernelSurvivalSet (blockRebasedInactive active query j θ n) k := hb
    rw [kernelSurvivalSet_eq_inter_before] at hp
    obtain ⟨hl',hu',hc⟩ := ih h.1 hl hu hp.2
    have hn : ¬active j θ (query (n+k) (historyRebase n k h.1)) := hp.1
    have he := blockComparisonIndex_eq_stage active query Θ j θ (n+k) (historyRebase n k h.1) hl' hu' hn
    have hindex : blockComparisonIndex active query (Function.update Θ j θ) (n+k) (historyRebase n k h.1)≤j.val := by
      rw [he]
      exact (blockActivationIndex_le active Θ _ j.val).2
    refine ⟨?_,?_,?_⟩
    · change j.val≤max (blockComparisonProgress active query (Function.update Θ j θ) (n+k) (historyRebase n k h.1))
        (blockComparisonIndex active query (Function.update Θ j θ) (n+k) (historyRebase n k h.1))+1
      exact hl'.trans (Nat.add_le_add_right (le_max_left _ _) 1)
    · exact max_le hu' hindex
    · change (if kernelChargeCount (blockStageSelected active (rebasedQuery query n) Θ j) cap k h.1<cap ∧
          blockStageSelected active (rebasedQuery query n) Θ j k h.1 then
          kernelChargeCount (blockStageSelected active (rebasedQuery query n) Θ j) cap k h.1+1 else
          kernelChargeCount (blockStageSelected active (rebasedQuery query n) Θ j) cap k h.1)≤
        blockStageCharges active query (Function.update Θ j θ) (n+k) (historyRebase n k h.1) j+
          blockChargeStep active query (Function.update Θ j θ) (n+k) (historyRebase n k h.1) j
      have hs : blockStageIndex active query Θ j (n+k) (historyRebase n k h.1)=
          blockStageIndex active (rebasedQuery query n) Θ j k h.1 := rfl
      simp only [blockChargeStep,he,hs,hu',and_true,blockStageSelected]
      split_ifs <;> omega

end
end SecondOrder
