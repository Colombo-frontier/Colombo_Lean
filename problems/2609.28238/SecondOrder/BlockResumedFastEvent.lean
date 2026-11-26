import SecondOrder.BlockResumedAgreement
import SecondOrder.BlockRebasedProgress

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

theorem kernelHiddenEvent_survival_iff (E : ∀ k, H → FiniteHistory S A k → Prop) :
    ∀ k (h : FiniteHistory (H × S) A k),
    h ∈ kernelSurvivalSet (fun m => (kernelHiddenEvent E m)ᶜ) k ↔
      finiteHistoryMapInitial Prod.snd k h ∈ kernelSurvivalSet
        (fun m => {p | ¬E m (finiteHistoryInitial k h).1 p}) k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro h
    change (¬E (k+1) (finiteHistoryInitial k h.1).1 (finiteHistoryMapInitial Prod.snd (k+1) h)) ∧
      h.1 ∈ kernelSurvivalSet (fun m => (kernelHiddenEvent E m)ᶜ) k ↔ _
    rw [ih]
    rfl

theorem kernelHiddenEvent_before_iff (E : ∀ k, H → FiniteHistory S A k → Prop)
    (k : ℕ) (h : FiniteHistory (H × S) A k) :
    h ∈ kernelBeforeSet (fun m => (kernelHiddenEvent E m)ᶜ) k ↔
      finiteHistoryMapInitial Prod.snd k h ∈ kernelBeforeSet
        (fun m => {p | ¬E m (finiteHistoryInitial k h).1 p}) k := by
  cases k with
  | zero => rfl
  | succ k => exact kernelHiddenEvent_survival_iff E k h.1

def blockResumedCharges (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n k : ℕ)
    (h : FiniteHistory (H × FiniteHistory S A n) A k) : ℕ :=
  blockStageCharges active query (Function.update Θ j (finiteHistoryInitial k h).1)
    (n+k) (historyRebase n k (finiteHistoryMapInitial Prod.snd k h)) j

def blockResumedEntryGood (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n : ℕ)
    (h : H × FiniteHistory S A n) : Prop :=
  j.val≤blockComparisonProgress active query (Function.update Θ j h.1) n h.2+1 ∧
    blockComparisonProgress active query (Function.update Θ j h.1) n h.2≤j.val

theorem blockResumed_before_invariants (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n cap k : ℕ)
    (h : FiniteHistory (H × FiniteHistory S A n) A k)
    (hg : blockResumedEntryGood active query Θ j n (finiteHistoryInitial k h))
    (hb : h ∈ kernelBeforeSet (fun m => (blockResumedActive active query j n m)ᶜ) k) :
    j.val≤blockResumedProgress active query Θ j n k h+1 ∧
    blockResumedProgress active query Θ j n k h≤j.val ∧
    kernelChargeCount (stageSelected (blockStageSelected active (rebasedQuery query n) Θ j)) cap k h≤
      blockResumedCharges active query Θ j n k h := by
  have he : finiteHistoryInitial k (finiteHistoryMapInitial Prod.snd k h)=(finiteHistoryInitial k h).2 :=
    historyInitial_map Prod.snd k h
  have hp := (kernelHiddenEvent_before_iff (fun k θ h => active j θ (rebasedQuery query n k h)) k h).mp hb
  have hi := blockRebased_before_invariants active query Θ j (finiteHistoryInitial k h).1 n cap k
    (finiteHistoryMapInitial Prod.snd k h) (by rw [he]; exact hg.1) (by rw [he]; exact hg.2) hp
  refine ⟨hi.1,hi.2.1,?_⟩
  change kernelChargeCount (fun k h => blockStageSelected active (rebasedQuery query n) Θ j k
    (finiteHistoryMapInitial Prod.snd k h)) cap k h≤_
  rw [kernelChargeCount_hidden]
  exact hi.2.2

/-- With fewer than cap actual charges, absence of a marked first
activation implies survival of every progress, inactivity, and cap test. -/
theorem blockResumed_noHit_survival (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n cap : ℕ) :
    ∀ k (h : FiniteHistory (H × FiniteHistory S A n) A k),
    blockResumedEntryGood active query Θ j n (finiteHistoryInitial k h) →
    blockResumedCharges active query Θ j n k h<cap →
    h ∉ kernelStoppedHitSet (blockResumedSafe active query Θ j n cap) (blockResumedActive active query j n) k →
    h ∈ kernelSurvivalSet (blockResumedSafe active query Θ j n cap) k := by
  intro k
  induction k with
  | zero =>
    intro h hg hc hn
    exact ⟨hg.1,hg.2,hn,lt_of_le_of_lt (Nat.zero_le _) hc⟩
  | succ k ih =>
    intro h hg hc hn
    have hprev : h.1 ∉ kernelStoppedHitSet (blockResumedSafe active query Θ j n cap)
        (blockResumedActive active query j n) k := fun hh => hn (Or.inl hh)
    have hcount : blockResumedCharges active query Θ j n k h.1<cap := by
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hc
    have hp := ih h.1 hg hcount hprev
    have hb : h ∈ kernelBeforeSet (blockResumedSafe active query Θ j n cap) (k+1) := hp
    have ha : h ∉ blockResumedActive active query j n (k+1) := fun hh => hn (Or.inr ⟨hb,hh⟩)
    have hba := kernelBeforeSet_mono (blockResumedSafe active query Θ j n cap)
      (fun m => (blockResumedActive active query j n m)ᶜ) (fun _ _ hh => hh.2.2.1) (k+1) hb
    obtain ⟨hl,hu,hcharge⟩ := blockResumed_before_invariants active query Θ j n cap (k+1) h hg hba
    exact ⟨⟨hl,hu,ha,lt_of_le_of_lt hcharge hc⟩,hp⟩

/-- A genuinely completed target with fewer than cap original charges
must appear in the stopped activation event of the resumed interaction. -/
theorem blockResumed_fastCompletion_subset (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n cap k : ℕ)
    (h : FiniteHistory (H × FiniteHistory S A n) A k)
    (hg : blockResumedEntryGood active query Θ j n (finiteHistoryInitial k h))
    (hc : blockResumedCharges active query Θ j n k h<cap)
    (hf : j.val<max (blockResumedProgress active query Θ j n k h)
      (blockComparisonIndex active query (Function.update Θ j (finiteHistoryInitial k h).1)
        (n+k) (historyRebase n k (finiteHistoryMapInitial Prod.snd k h)))) :
    h ∈ kernelStoppedHitSet (blockResumedSafe active query Θ j n cap) (blockResumedActive active query j n) k := by
  by_contra hn
  have hs := kernelSurvivalSet_subset _ k (blockResumed_noHit_survival active query Θ j n cap k h hg hc hn)
  have he := blockComparisonIndex_eq_stage active query Θ j (finiteHistoryInitial k h).1 (n+k)
    (historyRebase n k (finiteHistoryMapInitial Prod.snd k h)) hs.1 hs.2.1 hs.2.2.1
  have hi : blockComparisonIndex active query (Function.update Θ j (finiteHistoryInitial k h).1)
      (n+k) (historyRebase n k (finiteHistoryMapInitial Prod.snd k h))≤j.val := by
    rw [he]
    exact (blockActivationIndex_le active Θ _ j.val).2
  exact (not_lt_of_ge (max_le hs.2.1 hi)) hf

end
end SecondOrder
