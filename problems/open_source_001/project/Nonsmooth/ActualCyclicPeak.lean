import Nonsmooth.CyclicPeakBracket

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

abbrev CyclicPeakState := (Fin 4 → ℝ) × ((ℕ × ℤ) × ℝ × ℝ)

def cyclicPeakInitialState (N : ℕ) (v : Fin 4 → ℝ) : (ℕ × ℤ) × ℝ × ℝ :=
  ((N, (bestFourResponse v).val * 2 ^ N), 0, 0)

def cyclicPeakPolicy (N : ℕ) : Policy Unit CyclicPeakState ℤ where
  initial _ := (fun _ => 0, ((N, 0), 0, 0))
  query t _ st := if t < 4 then (t : ℤ) * 2 ^ N
    else (dyadicPeakPolicy N 0).query (t - 4) () st.2
  update t _ st y := if ht : t < 4 then
      let v := Function.update st.1 ⟨t, ht⟩ y
      if t = 3 then (v, cyclicPeakInitialState N v) else (v, st.2)
    else (st.1, (dyadicPeakPolicy N 0).update (t - 4) () st.2 y)
  output _ st := st.2.1.2

theorem cyclicPeakPolicy_initial_four (N : ℕ) (f : ℤ → ℝ) :
    (cyclicPeakPolicy N).run f () 4 =
      (fun i : Fin 4 => f ((i.val : ℤ) * 2 ^ N),
        cyclicPeakInitialState N (fun i : Fin 4 => f ((i.val : ℤ) * 2 ^ N))) := by
  have hv : Function.update (Function.update (Function.update
      (Function.update (fun _ : Fin 4 => (0 : ℝ)) 0 (f 0)) 1 (f (2 ^ N)))
        2 (f (2 * 2 ^ N))) 3 (f (3 * 2 ^ N)) =
      (fun i : Fin 4 => f ((i.val : ℤ) * 2 ^ N)) := by
    funext i
    fin_cases i <;> simp
  norm_num [Policy.run, cyclicPeakPolicy]
  exact ⟨hv, congrArg (cyclicPeakInitialState N) hv⟩

theorem cyclicPeakPolicy_run_exact (N n : ℕ) (f : ℤ → ℝ) :
    (cyclicPeakPolicy N).run f () (3 * n + 4) =
      (fun i : Fin 4 => f ((i.val : ℤ) * 2 ^ N),
        (dyadicPeakIter f N ((bestFourResponse (fun i => f ((i.val : ℤ) * 2 ^ N))).val * 2 ^ N) n,
          0, 0)) := by
  induction n with
  | zero => exact cyclicPeakPolicy_initial_four N f
  | succ n ih =>
    rw [show 3 * (n + 1) + 4 = ((3 * n + 4 + 1) + 1) + 1 by omega]
    generalize hk : 3 * n + 4 = k at ih ⊢
    simp only [Policy.run]
    simp only [ih]
    simp only [cyclicPeakPolicy,
      if_neg (show ¬k < 4 by omega), dif_neg (show ¬k < 4 by omega),
      if_neg (show ¬k + 1 < 4 by omega), dif_neg (show ¬k + 1 < 4 by omega),
      if_neg (show ¬k + 1 + 1 < 4 by omega), dif_neg (show ¬k + 1 + 1 < 4 by omega),
      dyadicPeakPolicy,
      show (k - 4) % 3 = 0 by omega,
      show ((k + 1) - 4) % 3 = 1 by omega,
      show ((k + 1 + 1) - 4) % 3 = 2 by omega,
      if_true, if_false, Nat.one_ne_zero, Nat.reduceEqDiff, dyadicPeakIter]

theorem cyclicPeakPolicy_result_exact (N : ℕ) (f : ℤ → ℝ) :
    (cyclicPeakPolicy N).result f () (3 * N + 4) = cyclicDyadicPeak f N := by
  unfold Policy.result
  rw [cyclicPeakPolicy_run_exact]
  have hi := dyadicPeakIter_search_invariant f N N
    ((bestFourResponse (fun i => f ((i.val : ℤ) * 2 ^ N))).val * 2 ^ N) le_rfl
  rw [dyadicPeakIter_remaining, Nat.sub_self] at hi
  exact hi

theorem cyclicPeakPolicy_local_max (N : ℕ) (f : ℤ → ℝ)
    (hp : Function.Periodic f (4 * 2 ^ N)) :
    let z := (cyclicPeakPolicy N).result f () (3 * N + 4)
    f (z - 1) ≤ f z ∧ f (z + 1) ≤ f z := by
  dsimp only
  rw [cyclicPeakPolicy_result_exact]
  exact cyclicDyadicPeak_local_max f N hp

end
end Nonsmooth
