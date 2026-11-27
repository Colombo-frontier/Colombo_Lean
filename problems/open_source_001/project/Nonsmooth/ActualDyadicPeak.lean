import Nonsmooth.DyadicPeakSearch

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def dyadicPeakUpdate (st : ℕ × ℤ) (l v r : ℝ) : ℕ × ℤ :=
  (st.1 - 1, dyadicPeakCenter st.2 (2 ^ (st.1 - 1)) l v r)

def dyadicPeakIter (f : ℤ → ℝ) (N : ℕ) (c : ℤ) : ℕ → ℕ × ℤ
  | 0 => (N, c)
  | n + 1 => let st := dyadicPeakIter f N c n
      dyadicPeakUpdate st (f (st.2 - 2 ^ (st.1 - 1))) (f st.2)
        (f (st.2 + 2 ^ (st.1 - 1)))

/-- Each refinement uses three separately charged values; no initial value is supplied for free. -/
def dyadicPeakPolicy (N : ℕ) (c : ℤ) : Policy Unit ((ℕ × ℤ) × ℝ × ℝ) ℤ where
  initial _ := ((N, c), 0, 0)
  query t _ st := if t % 3 = 0 then st.1.2 - 2 ^ (st.1.1 - 1)
    else if t % 3 = 1 then st.1.2 else st.1.2 + 2 ^ (st.1.1 - 1)
  update t _ st y := if t % 3 = 0 then (st.1, y, 0)
    else if t % 3 = 1 then (st.1, st.2.1, y)
    else (dyadicPeakUpdate st.1 st.2.1 st.2.2 y, 0, 0)
  output _ st := st.1.2

theorem dyadicPeakPolicy_run_exact (N n : ℕ) (c : ℤ) (f : ℤ → ℝ) :
    (dyadicPeakPolicy N c).run f () (3 * n) = (dyadicPeakIter f N c n, 0, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by omega]
    simp only [Policy.run]
    simp only [ih]
    simp only [dyadicPeakPolicy,
      show (3 * n) % 3 = 0 by omega,
      show (3 * n + 1) % 3 = 1 by omega,
      show (3 * n + 1 + 1) % 3 = 2 by omega,
      if_true, if_false, Nat.one_ne_zero, Nat.reduceEqDiff, dyadicPeakIter]

theorem dyadicPeakIter_remaining (f : ℤ → ℝ) (N n : ℕ) (c : ℤ) :
    (dyadicPeakIter f N c n).1 = N - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (dyadicPeakIter f N c n).1 - 1 = N - (n + 1)
    rw [ih]
    omega

theorem dyadicPeakSearch_step (f : ℤ → ℝ) {r : ℕ} (hr : 0 < r) (c : ℤ) :
    dyadicPeakSearch f r c = dyadicPeakSearch f (r - 1)
      (dyadicPeakCenter c (2 ^ (r - 1)) (f (c - 2 ^ (r - 1))) (f c)
        (f (c + 2 ^ (r - 1)))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rfl

theorem dyadicPeakIter_search_invariant (f : ℤ → ℝ) (N n : ℕ) (c : ℤ) (hn : n ≤ N) :
    dyadicPeakSearch f (dyadicPeakIter f N c n).1 (dyadicPeakIter f N c n).2 =
      dyadicPeakSearch f N c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ≤ N := by omega
    have hp : 0 < (dyadicPeakIter f N c n).1 := by
      rw [dyadicPeakIter_remaining]
      omega
    change dyadicPeakSearch f ((dyadicPeakIter f N c n).1 - 1)
      (dyadicPeakCenter (dyadicPeakIter f N c n).2 (2 ^ ((dyadicPeakIter f N c n).1 - 1))
        (f ((dyadicPeakIter f N c n).2 - 2 ^ ((dyadicPeakIter f N c n).1 - 1)))
        (f (dyadicPeakIter f N c n).2)
        (f ((dyadicPeakIter f N c n).2 + 2 ^ ((dyadicPeakIter f N c n).1 - 1)))) = _
    exact (dyadicPeakSearch_step f hp _).symm.trans (ih hn')

theorem dyadicPeakPolicy_result_exact (N : ℕ) (c : ℤ) (f : ℤ → ℝ) :
    (dyadicPeakPolicy N c).result f () (3 * N) = dyadicPeakSearch f N c := by
  unfold Policy.result
  rw [dyadicPeakPolicy_run_exact]
  have hi := dyadicPeakIter_search_invariant f N N c le_rfl
  rw [dyadicPeakIter_remaining, Nat.sub_self] at hi
  exact hi

theorem dyadicPeakPolicy_local_max (N : ℕ) (c : ℤ) (f : ℤ → ℝ)
    (hl : f (c - 2 ^ N) ≤ f c) (hr : f (c + 2 ^ N) ≤ f c) :
    let z := (dyadicPeakPolicy N c).result f () (3 * N)
    f (z - 1) ≤ f z ∧ f (z + 1) ≤ f z := by
  dsimp only
  rw [dyadicPeakPolicy_result_exact]
  exact dyadicPeakSearch_local_max f N c hl hr

end
end Nonsmooth
