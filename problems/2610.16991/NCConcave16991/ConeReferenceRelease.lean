import NCConcave16991.ConeReferencePhase

/-! # Exact row release and source caches at the cone-machine boundaries -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

def freeState (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) : State E n M R hR :=
  runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 2 + k)

theorem freeState_phase (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n) :
    (freeState E n M R hR P seed hn q rows t k).phase.val = 2 + k := by
  simpa only [freeState, Nat.add_assoc] using
    run_cycle_phase E n M R hR P seed hn q rows t (2 + k) (by omega)

theorem freeState_release (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k ≤ n) :
    (freeState E n M R hR P seed hn q rows t k).release =
      (freeState E n M R hR P seed hn q rows t 0).release := by
  exact congrArg (fun d : FreeData E n M R hR ↦ d.2.2.2.2)
    (run_freeData E n M R hR P seed hn q rows t k hk)

theorem freeState_pendingStage (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k ≤ n) :
    (freeState E n M R hR P seed hn q rows t k).pendingStage =
      (freeState E n M R hR P seed hn q rows t 0).pendingStage := by
  exact congrArg (fun d : FreeData E n M R hR ↦ d.2.2.2.1)
    (run_freeData E n M R hR P seed hn q rows t k hk)

theorem freeState_stageIndex (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k ≤ n) :
    stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t k) =
      stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0) := by
  apply Fin.ext
  simp only [stageIndex, freeState_pendingStage E n M R hR P seed hn q rows t k hk]

theorem freeState_succ (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n) :
    freeState E n M R hR P seed hn q rows t (k + 1) =
      freeUpdate E n M R hR hn (freeState E n M R hR P seed hn q rows t k)
        (requestedAnswer E n M rows (request E n M R hR hn
          (freeState E n M R hR P seed hn q rows t k))) := by
  have hp := freeState_phase E n M R hR P seed hn q rows t k hk
  change runWithRows E n M R hR P seed hn q rows (((n + 2) * t + 2 + k) + 1) = _
  rw [runWithRows, stepWithRows, update]
  change (if (freeState E n M R hR P seed hn q rows t k).phase.val = 0 then _ else
    if (freeState E n M R hR P seed hn q rows t k).phase.val = 1 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

theorem freeState_rows_succ (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n) :
    (freeState E n M R hR P seed hn q rows t (k + 1)).rows =
      if (freeState E n M R hR P seed hn q rows t 0).release = true ∧
          (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 then
        ConeReferenceCache.putRow (freeState E n M R hR P seed hn q rows t k).rows
          (stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0))
          ⟨k, hk⟩ (rows (stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0)) ⟨k, hk⟩)
      else (freeState E n M R hR P seed hn q rows t k).rows := by
  have hp := freeState_phase E n M R hR P seed hn q rows t k hk
  have hr := freeState_release E n M R hR P seed hn q rows t k hk.le
  have hs := freeState_pendingStage E n M R hR P seed hn q rows t k hk.le
  have hj := freeState_stageIndex E n M R hR P seed hn q rows t k hk.le
  have hi : releaseRow E n M R hR hn (freeState E n M R hR P seed hn q rows t k) = ⟨k, hk⟩ := by
    apply Fin.ext
    simp only [releaseRow, hp, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hk]
  rw [freeState_succ E n M R hR P seed hn q rows t k hk]
  simp only [freeUpdate, request, requestOfSummary, hp, show 2 + k ≠ 0 by omega,
    show 2 + k ≠ 1 by omega, ite_false, hr, hs]
  split_ifs <;> simp_all [requestedAnswer, stageIndex,
    releaseRow, hp, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hk]

theorem freeState_rows (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k ≤ n)
    (j : Fin (M + 1)) (i : Fin n) :
    (freeState E n M R hR P seed hn q rows t k).rows j i =
      if (freeState E n M R hR P seed hn q rows t 0).release = true ∧
          (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 ∧
          j = stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0) ∧ i.val < k then
        rows j i
      else (freeState E n M R hR P seed hn q rows t 0).rows j i := by
  induction k with
  | zero => simp only [not_lt_zero', and_false, ite_false]
  | succ k ih =>
      rw [freeState_rows_succ E n M R hR P seed hn q rows t k (by omega)]
      by_cases ha : (freeState E n M R hR P seed hn q rows t 0).release = true ∧
          (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1
      · rw [if_pos ha]
        by_cases hj : j = stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0)
        · subst j
          by_cases hi : i.val = k
          · have he : i = (⟨k, by omega⟩ : Fin n) := Fin.ext hi
            rw [he]
            simp only [ConeReferenceCache.putRow_same, ha.1, ha.2, true_and, and_self, Fin.val_mk]
            rw [if_pos (by omega)]
          · have he : i ≠ (⟨k, by omega⟩ : Fin n) := fun h ↦ hi (congrArg Fin.val h)
            simp only [ConeReferenceCache.putRow, Function.update_self, Function.update_of_ne he]
            rw [ih (by omega)]
            simp only [ha.1, ha.2, true_and, and_self, Fin.val_mk]
            simp only [show (i.val < k) ↔ (i.val < k + 1) by omega]
        · rw [ConeReferenceCache.putRow_other_stage _ _ _ _ _ hj, ih (by omega)]
          simp only [hj, false_and, and_false, ite_false]
      · rw [if_neg ha, ih (by omega)]
        simp only [show ¬((freeState E n M R hR P seed hn q rows t 0).release = true ∧
            (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 ∧
            j = stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0) ∧ i.val < k) by tauto,
          show ¬((freeState E n M R hR P seed hn q rows t 0).release = true ∧
            (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 ∧
            j = stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0) ∧ i.val < k + 1) by tauto,
          ite_false]

theorem freeState_means_succ (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n) :
    (freeState E n M R hR P seed hn q rows t (k + 1)).means =
      if (freeState E n M R hR P seed hn q rows t 0).release = true ∧
          (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 ∧ k + 1 = n then
        ConeReferenceCache.releaseMean (freeState E n M R hR P seed hn q rows t (k + 1)).rows
          (freeState E n M R hR P seed hn q rows t k).means
          (stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0))
      else (freeState E n M R hR P seed hn q rows t k).means := by
  rw [freeState_rows_succ E n M R hR P seed hn q rows t k hk]
  have hp := freeState_phase E n M R hR P seed hn q rows t k hk
  have hr := freeState_release E n M R hR P seed hn q rows t k hk.le
  have hs := freeState_pendingStage E n M R hR P seed hn q rows t k hk.le
  have hi : releaseRow E n M R hR hn (freeState E n M R hR P seed hn q rows t k) = ⟨k, hk⟩ := by
    apply Fin.ext
    simp only [releaseRow, hp, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hk]
  rw [freeState_succ E n M R hR P seed hn q rows t k hk]
  simp only [freeUpdate, request, requestOfSummary, hp, show 2 + k ≠ 0 by omega,
    show 2 + k ≠ 1 by omega, ite_false, hr, hs]
  split_ifs <;> simp_all [requestedAnswer, stageIndex, releaseRow, Nat.mod_eq_of_lt hk]
  all_goals omega

theorem freeState_means_before_last (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n) :
    (freeState E n M R hR P seed hn q rows t k).means =
      (freeState E n M R hR P seed hn q rows t 0).means := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [freeState_means_succ E n M R hR P seed hn q rows t k (by omega),
        if_neg (by omega), ih (by omega)]

theorem freeState_final_means (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (freeState E n M R hR P seed hn q rows t n).means =
      if (freeState E n M R hR P seed hn q rows t 0).release = true ∧
          (freeState E n M R hR P seed hn q rows t 0).pendingStage < M + 1 then
        ConeReferenceCache.releaseMean rows (freeState E n M R hR P seed hn q rows t 0).means
          (stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0))
      else (freeState E n M R hR P seed hn q rows t 0).means := by
  have hk : n - 1 < n := by omega
  have he : n - 1 + 1 = n := by omega
  have hs := freeState_means_succ E n M R hR P seed hn q rows t (n - 1) hk
  rw [he, freeState_means_before_last E n M R hR P seed hn q rows t (n - 1) hk] at hs
  simp only [and_true] at hs
  rw [hs]
  split_ifs with ha
  · unfold ConeReferenceCache.releaseMean
    apply congrArg (fun a : E ↦ ConeReferenceCache.putMean
      (freeState E n M R hR P seed hn q rows t 0).means
      (stageIndex E n M R hR (freeState E n M R hR P seed hn q rows t 0)) a)
    unfold ConeReferenceCache.rowMeanAt
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [freeState_rows E n M R hR P seed hn q rows t n le_rfl]
    simp only [ha.1, ha.2, true_and, i.isLt, ite_true]
  · rfl

theorem freeState_final_eq_boundary (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    freeState E n M R hR P seed hn q rows t n = boundary E n M R hR P seed hn q rows (t + 1) := by
  unfold freeState boundary
  congr 1
  ring

end

end NCConcave16991.Haar.ConeMachine
