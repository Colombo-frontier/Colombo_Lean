import Bilevel.PolishedLiteralObserverRun

/-! The source flat counter reveals one micro column on every success
and one macro column only when a whole micro block is completed. -/
noncomputable section
namespace Bilevel.PolishedLiteralActualObserver
set_option autoImplicit false

def microSchedule (K : ℕ) : PrefixSchedule K where
  count a := min K a
  zero := by simp
  bound _ := min_le_left _ _
  monotone := fun _ _ h => min_le_min_left K h
  one_step a := by omega

def macroSchedule (S M : ℕ) : PrefixSchedule S where
  count a := min S (a/M)
  zero := by simp
  bound _ := min_le_left _ _
  monotone := fun _ _ h => min_le_min_left S (Nat.div_le_div_right h)
  one_step a := by
    have h : (a+1)/M≤a/M+1 := by
      rw [Nat.succ_div]
      split <;> omega
    omega

/-- Capping the actual flat counter at the number of available columns
has exactly the source quotient used by the macro observer. -/
theorem macroSchedule_count (S M a : ℕ) (hM : 0<M) :
    (macroSchedule S M).count a=min a (S*M)/M := by
  change min S (a/M)=min a (S*M)/M
  by_cases ha : a≤S*M
  · rw [min_eq_left ha]
    have hd : a/M≤S := (Nat.div_le_div_right ha).trans (by simp [hM.ne'])
    exact min_eq_right hd
  · rw [min_eq_right (by omega : S*M≤a)]
    have hd : S≤a/M := by
      have := Nat.div_le_div_right (c:=M) (le_of_not_ge ha)
      simpa [hM.ne'] using this
    rw [min_eq_left hd]
    simp [hM.ne']

end Bilevel.PolishedLiteralActualObserver
