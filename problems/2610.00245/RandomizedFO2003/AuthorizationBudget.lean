import RandomizedFO2003.MarkedQueryDepth

namespace RandomizedFO2003.Rotations

/-- A query can have seen at most one marked power per elapsed round,
including the current authorization and excluding the current matrix answer. -/
theorem markedQueryDepth_le_index (t : ℕ) (a : Fin t → Bool) (i : Fin t) :
    markedQueryDepth t a 0 i ≤ i.val + 1 := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases ha : a 0 <;> simp [markedQueryDepth, LatentOperation.nextDepth, ha]
    · cases ha : a 0
      · have hh := ih (fun j => a j.succ) j
        simp only [markedQueryDepth, Fin.cons_succ, ha, LatentOperation.nextDepth] at *
        simp only [Fin.val_succ]
        omega
      · change markedQueryDepth t (fun j => a j.succ)
          (LatentOperation.matrix.nextDepth ((LatentOperation.mark (a 0)).nextDepth 0)) j ≤ _
        rw [ha]
        change markedQueryDepth t (fun j => a j.succ) 2 j ≤ _
        rw [markedQueryDepth_positive t _ 2 (by omega)]
        simp only [Fin.val_succ]
        omega

/-- A whole initial interval with no authorization delays the available
degree at every later query. No first-authorization index need be selected. -/
theorem markedQueryDepth_le_of_unauthorized_before (t : ℕ) (a : Fin t → Bool) (τ : ℕ)
    (ha : ∀ j : Fin t, j.val < τ → a j = false) (i : Fin t) :
    markedQueryDepth t a 0 i ≤ i.val + 1 - τ := by
  induction t generalizing τ with
  | zero => exact i.elim0
  | succ t ih =>
    cases τ with
    | zero => simpa only [Nat.sub_zero] using markedQueryDepth_le_index (t + 1) a i
    | succ τ =>
      have hzero : a 0 = false := ha 0 (by simp)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [markedQueryDepth, hzero, LatentOperation.nextDepth]
      · have hh := ih (fun k => a k.succ) τ
          (fun k hk => ha k.succ (by simp only [Fin.val_succ]; omega)) j
        change markedQueryDepth t (fun k => a k.succ)
          (LatentOperation.matrix.nextDepth ((LatentOperation.mark (a 0)).nextDepth 0)) j ≤ _
        rw [hzero]
        change markedQueryDepth t (fun k => a k.succ) 0 j ≤ _
        simp only [Fin.val_succ]
        omega

end RandomizedFO2003.Rotations
