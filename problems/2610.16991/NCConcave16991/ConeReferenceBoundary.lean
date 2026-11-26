import NCConcave16991.ConeReferenceSupport

/-! # Exact completed-stage caches at every real-query boundary -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

theorem paidUpdate_means (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) :
    (paidUpdate E n M R hR hn q s a).means = s.means := by
  unfold paidUpdate paidQuery
  split_ifs <;> rfl

theorem paidUpdate_past_rows (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E)
    (hs : s.pendingStage = s.progress.1) (j : Fin (M + 1)) (hj : j.val < s.progress.1) :
    (paidUpdate E n M R hR hn q s a).rows j = s.rows j := by
  unfold paidUpdate paidQuery
  split_ifs with hquery hvalid
  · apply ConeReferenceCache.putRow_other_stage
    intro he
    have hv := congrArg Fin.val he
    change j.val = s.pendingStage % (M + 1) at hv
    rw [Nat.mod_eq_of_lt hvalid, hs] at hv
    omega
  · rfl
  · rfl

theorem paidUpdate_release_valid (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E)
    (hr : (paidUpdate E n M R hR hn q s a).release = true) : s.pendingStage < M + 1 := by
  unfold paidUpdate paidQuery at hr
  split_ifs at hr <;> simp_all

theorem paidUpdate_frontier (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) :
    (paidUpdate E n M R hR hn q s a).progress.1 =
      if (paidUpdate E n M R hR hn q s a).release = true then s.progress.1 + 1 else s.progress.1 := by
  by_cases hquery : actionIsQuery E n M R hR s.pending = true
  · simp only [paidUpdate, hquery, ite_true]
    by_cases hvalid : s.pendingStage < M + 1
    · simp only [paidQuery, hvalid, ite_true]
      change (ConeCounter.step s.progress (some (actionQuery E n M R hR hn s.pending).1)).1 =
        if shouldRelease n s.progress (actionQuery E n M R hR hn s.pending).1 = true then
          s.progress.1 + 1 else s.progress.1
      simp only [shouldRelease, decide_eq_true_eq, ConeCounter.step]
      split_ifs <;> rfl
    · simp only [paidQuery, hvalid, ite_false, Bool.false_eq_true, ite_false]
  · simp only [paidUpdate, hquery, ite_false, Bool.false_eq_true, ite_false]

def PastCorrect (source : Fin (M + 1) → Fin n → E) (s : State E n M R hR) : Prop :=
  ∀ j : Fin (M + 1), j.val < s.progress.1 →
    s.rows j = source j ∧ s.means j = ConeReferenceCache.rowMeanAt source j

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

theorem freeState_zero_eq_paid (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    freeState E n M R hR P seed hn q rows t 0 =
      paidUpdate E n M R hR hn q
        (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t))
        (requestedAnswer E n M rows (request E n M R hR hn
          (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t)))) := by
  exact run_paid E n M R hR P seed hn q rows t

theorem freeState_zero_pendingStage (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (freeState E n M R hR P seed hn q rows t 0).pendingStage =
      (boundary E n M R hR P seed hn q rows t).progress.1 := by
  rw [freeState_zero_eq_paid, paidUpdate_pendingStage]
  rfl

theorem freeState_zero_means (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (freeState E n M R hR P seed hn q rows t 0).means =
      (boundary E n M R hR P seed hn q rows t).means := by
  rw [freeState_zero_eq_paid, paidUpdate_means]
  rfl

theorem freeState_zero_past_rows (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ)
    (j : Fin (M + 1)) (hj : j.val < (boundary E n M R hR P seed hn q rows t).progress.1) :
    (freeState E n M R hR P seed hn q rows t 0).rows j =
      (boundary E n M R hR P seed hn q rows t).rows j := by
  rw [freeState_zero_eq_paid]
  exact paidUpdate_past_rows E n M R hR hn q _ _ rfl j hj

theorem boundary_pastCorrect (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    PastCorrect E n M R hR rows (boundary E n M R hR P seed hn q rows t) := by
  induction t with
  | zero => intro j hj; change j.val < 0 at hj; omega
  | succ t ih =>
      intro j hj
      have hprogress := congrArg (fun d : FreeData E n M R hR ↦ d.2.1)
        (run_freeData E n M R hR P seed hn q rows t n le_rfl)
      dsimp only [freeData] at hprogress
      change (freeState E n M R hR P seed hn q rows t n).progress =
        (freeState E n M R hR P seed hn q rows t 0).progress at hprogress
      rw [← freeState_final_eq_boundary] at hj ⊢
      rw [hprogress] at hj
      have hstage := freeState_zero_pendingStage E n M R hR P seed hn q rows t
      have hfront := paidUpdate_frontier E n M R hR hn q
        (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t))
        (requestedAnswer E n M rows (request E n M R hR hn
          (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t))))
      rw [← freeState_zero_eq_paid] at hfront
      change (freeState E n M R hR P seed hn q rows t 0).progress.1 =
        if (freeState E n M R hR P seed hn q rows t 0).release = true then
          (boundary E n M R hR P seed hn q rows t).progress.1 + 1 else
          (boundary E n M R hR P seed hn q rows t).progress.1 at hfront
      by_cases hrel : (freeState E n M R hR P seed hn q rows t 0).release = true
      · have hvalid : (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 := by
          rw [freeState_zero_eq_paid, paidUpdate_pendingStage]
          apply paidUpdate_release_valid E n M R hR hn q _ _
          rwa [← freeState_zero_eq_paid]
        rw [if_pos hrel] at hfront
        have hindex : (stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0)).val =
            (boundary E n M R hR P seed hn q rows t).progress.1 := by
          change (freeState E n M R hR P seed hn q rows t 0).pendingStage % (M + 1) = _
          rw [Nat.mod_eq_of_lt hvalid, hstage]
        by_cases hjold : j.val < (boundary E n M R hR P seed hn q rows t).progress.1
        · have hjne : j ≠ stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0) := by
            intro he; have := congrArg Fin.val he; omega
          constructor
          · funext i
            rw [freeState_rows E n M R hR P seed hn q rows t n le_rfl]
            simp only [hrel, hvalid, hjne, false_and, and_false, ite_false]
            rw [freeState_zero_past_rows E n M R hR P seed hn q rows t j hjold]
            exact congrFun (ih j hjold).1 i
          · rw [freeState_final_means, if_pos ⟨hrel, hvalid⟩]
            rw [ConeReferenceCache.releaseMean, ConeReferenceCache.putMean_other _ _ _ _ hjne,
              freeState_zero_means]
            exact (ih j hjold).2
        · have hje : j = stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0) := by
            apply Fin.ext; omega
          constructor
          · funext i
            rw [freeState_rows E n M R hR P seed hn q rows t n le_rfl]
            simp only [hrel, hvalid, hje, true_and, i.isLt, ite_true]
          · rw [freeState_final_means, if_pos ⟨hrel, hvalid⟩]
            subst j
            exact ConeReferenceCache.putMean_same _ _ _
      · rw [if_neg hrel] at hfront
        have hjold : j.val < (boundary E n M R hR P seed hn q rows t).progress.1 := by omega
        constructor
        · funext i
          rw [freeState_rows E n M R hR P seed hn q rows t n le_rfl]
          simp only [hrel, false_and, ite_false]
          rw [freeState_zero_past_rows E n M R hR P seed hn q rows t j hjold]
          exact congrFun (ih j hjold).1 i
        · rw [freeState_final_means, if_neg (by tauto), freeState_zero_means]
          exact (ih j hjold).2

end

end NCConcave16991.Haar.ConeMachine
