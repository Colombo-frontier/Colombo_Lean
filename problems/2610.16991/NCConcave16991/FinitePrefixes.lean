import NCConcave16991.FiniteOutput
import NCConcave16991.FiniteFailure

/-! # Chronological prefixes, trajectories and adaptive failure checks -/

namespace NCConcave16991.FiniteProcess

variable {I : Type*} [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]

theorem historyPrefix_self (T : ℕ) (h : History I T) :
    historyPrefix T T le_rfl h = h := by
  cases T with
  | zero => rfl
  | succ T => simp [historyPrefix]

theorem historyPrefix_trans {s t T : ℕ} (hst : s ≤ t) (htT : t ≤ T)
    (h : History I T) :
    historyPrefix s T (hst.trans htT) h =
      historyPrefix s t hst (historyPrefix t T htT h) := by
  induction T generalizing t s with
  | zero =>
    have ht : t = 0 := by omega
    have hs : s = 0 := by omega
    subst t
    subst s
    rfl
  | succ T ih =>
    by_cases heq : t = T + 1
    · subst t
      rw [historyPrefix_self]
    · have ht : t ≤ T := by omega
      have hsne : s ≠ T + 1 := by omega
      simpa only [historyPrefix, heq, hsne, dite_false] using ih hst ht h.1

theorem historyPrefix_before_last (t : ℕ) (h : History I (t + 1)) :
    historyPrefix t (t + 1) (by omega) h = h.1 := by
  have hne : t ≠ t + 1 := by omega
  simp only [historyPrefix, hne, dite_false]
  exact historyPrefix_self t h.1

theorem historyPrefix_succ_fst {t T : ℕ} (ht : t + 1 ≤ T) (h : History I T) :
    (historyPrefix (t + 1) T ht h).1 = historyPrefix t T (by omega) h := by
  have hh := historyPrefix_trans (show t ≤ t + 1 by omega) ht h
  rw [historyPrefix_before_last] at hh
  exact hh.symm

theorem everBad_of_prefix (bad : (t : ℕ) → History I t → I → Prop)
    {t T : ℕ} (ht : t ≤ T) (h : History I T)
    (hb : everBad bad t (historyPrefix t T ht h)) : everBad bad T h := by
  induction T generalizing t with
  | zero =>
    have ht0 : t = 0 := by omega
    subst t
    exact hb
  | succ T ih =>
    by_cases heq : t = T + 1
    · subst t
      simpa only [historyPrefix_self] using hb
    · have ht' : t ≤ T := by omega
      have hb' : everBad bad t (historyPrefix t T ht' h.1) := by
        simpa only [historyPrefix, heq, dite_false] using hb
      exact Or.inl (ih ht' h.1 hb')

theorem noBad_prefix (bad : (t : ℕ) → History I t → I → Prop)
    {t T : ℕ} (ht : t ≤ T) (h : History I T) (hb : ¬everBad bad T h) :
    ¬everBad bad t (historyPrefix t T ht h) := fun hn ↦ hb (everBad_of_prefix bad ht h hn)

theorem noBad_step (bad : (t : ℕ) → History I t → I → Prop)
    {t T : ℕ} (ht : t + 1 ≤ T) (h : History I T) (hb : ¬everBad bad T h) :
    ¬bad t (historyPrefix t T (by omega) h) (historyPrefix (t + 1) T ht h).2 := by
  have hh := noBad_prefix bad ht h hb
  intro hstep
  apply hh
  apply Or.inr
  rw [historyPrefix_succ_fst]
  exact hstep

end NCConcave16991.FiniteProcess
