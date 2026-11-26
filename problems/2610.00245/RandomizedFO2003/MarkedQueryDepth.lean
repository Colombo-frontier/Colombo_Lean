import RandomizedFO2003.MarkedDepth

namespace RandomizedFO2003.Rotations

/-- Marked powers available at each inverse query, before that round's
matrix response. The depth is unaffected by any later authorization. -/
def markedQueryDepth : (t : ℕ) → (Fin t → Bool) → ℕ → Fin t → ℕ
  | 0, _, _ => Fin.elim0
  | t + 1, a, m => Fin.cons ((LatentOperation.mark (a 0)).nextDepth m)
      (markedQueryDepth t (fun i => a i.succ)
        (LatentOperation.matrix.nextDepth ((LatentOperation.mark (a 0)).nextDepth m)))

theorem markedQueryDepth_positive (t : ℕ) (a : Fin t → Bool) (m : ℕ) (hm : 0 < m) (i : Fin t) :
    markedQueryDepth t a m i = m + i.val := by
  induction t generalizing m with
  | zero => exact i.elim0
  | succ t ih =>
    have hs : (LatentOperation.mark (a 0)).nextDepth m = m := by
      cases a 0 <;> simp [LatentOperation.nextDepth, Nat.max_eq_left (by omega : 1 ≤ m)]
    have hmstep : LatentOperation.matrix.nextDepth m = m + 1 := by
      cases m with
      | zero => omega
      | succ m => rfl
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [markedQueryDepth, hs]
    · simp only [markedQueryDepth, Fin.cons_succ, hs, hmstep]
      rw [ih (fun i => a i.succ) (m + 1) (by omega) j]
      simp only [Fin.val_succ]
      omega

theorem markedQueryDepth_unauthorized (t : ℕ) (a : Fin t → Bool) (ha : ∀ i, a i = false)
    (i : Fin t) : markedQueryDepth t a 0 i = 0 := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [markedQueryDepth, ha 0, LatentOperation.nextDepth]
    · simpa only [markedQueryDepth, Fin.cons_succ, ha 0, LatentOperation.nextDepth] using
        ih (fun i => a i.succ) (fun i => ha i.succ) j

/-- An authorization at round τ creates exactly one marked power at that
round's query; each intervening matrix response adds one further power. -/
theorem markedQueryDepth_first_authorization (t : ℕ) (a : Fin t → Bool) (τ i : Fin t)
    (hfirst : a τ = true) (hearlier : ∀ j : Fin t, j.val < τ.val → a j = false)
    (hτi : τ.val ≤ i.val) : markedQueryDepth t a 0 i = i.val - τ.val + 1 := by
  induction t with
  | zero => exact τ.elim0
  | succ t ih =>
    revert hfirst hearlier hτi
    refine Fin.cases ?_ (fun k => ?_) τ
    · intro hfirst hearlier hτi
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [markedQueryDepth, hfirst, LatentOperation.nextDepth]
      · simp only [markedQueryDepth, Fin.cons_succ, hfirst, LatentOperation.nextDepth]
        change markedQueryDepth t (fun i => a i.succ) 2 j = _
        rw [markedQueryDepth_positive t _ 2 (by omega)]
        simp only [Fin.val_zero, Fin.val_succ]
        omega
    · intro hfirst hearlier hτi
      have hzero : a 0 = false := hearlier 0 (by simp)
      revert hτi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hτi
        simp only [Fin.val_zero, Fin.val_succ] at hτi
        omega
      · intro hτi
        simp only [markedQueryDepth, Fin.cons_succ, hzero, LatentOperation.nextDepth]
        rw [ih (fun j => a j.succ) k j hfirst
          (fun j hj => hearlier j.succ (by simpa using hj))
          (by simpa using hτi)]
        simp only [Fin.val_succ]
        omega

/-- Even if the transcript is authorized later, all earlier queries have
zero marked depth. This is stronger than a bound conditional on final depth. -/
theorem markedQueryDepth_before_authorization (t : ℕ) (a : Fin t → Bool) (i : Fin t)
    (hearlier : ∀ j : Fin t, j.val ≤ i.val → a j = false) : markedQueryDepth t a 0 i = 0 := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
    revert hearlier
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hearlier
      simp [markedQueryDepth, hearlier 0 le_rfl, LatentOperation.nextDepth]
    · intro hearlier
      have hzero : a 0 = false := hearlier 0 (by simp)
      simp only [markedQueryDepth, Fin.cons_succ, hzero, LatentOperation.nextDepth]
      exact ih (fun k => a k.succ) j (fun k hk => hearlier k.succ (by simpa using hk))

end RandomizedFO2003.Rotations
