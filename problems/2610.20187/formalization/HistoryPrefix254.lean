import Aggregation254
import Energy254

noncomputable section
namespace Paper254

/-- Prefix potential telescope for a history born at real time i>0.
The inputs are its birth mass, survival update and the already derived
one-step log-weight inequality; no prefix regret bound is assumed. -/
theorem history_prefix_log_bound (n : ℕ) (i q lam : ℝ) (p raw r : ℕ → ℝ)
    (hi : 0 < i) (hq : 0 < q) (hbirth : q/i ≤ p 0)
    (hp : ∀ t ≤ n, 0 < p t) (hr : ∀ t ≤ n, 0 < raw t)
    (hsurvive : ∀ t < n, (i+t)/(i+t+1)*raw t ≤ p (t+1))
    (hstep : ∀ t ≤ n, lam*r t ≤ Real.log (raw t)-Real.log (p t)) :
    lam*cumulative r (n+1) ≤ Real.log (raw n)+Real.log ((i+n)/q) := by
  induction n with
  | zero =>
    have hb := Real.log_le_log (div_pos hq hi) hbirth
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hi)] at hb
    have hs := hstep 0 (le_refl _)
    simp only [cumulative, Nat.zero_add, Finset.sum_range_one, Nat.cast_zero, add_zero,
      Real.log_div (ne_of_gt hi) (ne_of_gt hq)]
    linarith
  | succ n ih =>
    have hprev := ih (fun t ht => hp t (Nat.le_step ht))
      (fun t ht => hr t (Nat.le_step ht))
      (fun t ht => hsurvive t (Nat.lt.step ht))
      (fun t ht => hstep t (Nat.le_step ht))
    have ha : 0 < i+n := by positivity
    have hb : 0 < i+n+1 := by positivity
    have hm := Real.log_le_log
      (mul_pos (div_pos ha hb) (hr n (by omega))) (hsurvive n (by omega))
    rw [Real.log_mul (ne_of_gt (div_pos ha hb)) (ne_of_gt (hr n (by omega))),
      Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at hm
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hq)] at hprev
    have hlast := hstep (n+1) (le_refl _)
    rw [cumulative_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show i+((n : ℝ)+1) = i+n+1 by ring,
      Real.log_div (ne_of_gt hb) (ne_of_gt hq)]
    nlinarith

theorem history_prefix_overhead (n : ℕ) (i q lam : ℝ) (p raw r : ℕ → ℝ)
    (hi : 0 < i) (hq : 0 < q) (hlam : 0 < lam) (hbirth : q/i ≤ p 0)
    (hp : ∀ t ≤ n, 0 < p t) (hr : ∀ t ≤ n, 0 < raw t)
    (hsurvive : ∀ t < n, (i+t)/(i+t+1)*raw t ≤ p (t+1))
    (hstep : ∀ t ≤ n, lam*r t ≤ Real.log (raw t)-Real.log (p t))
    (hterminal : raw n ≤ 1) :
    cumulative r (n+1) ≤ Real.log ((i+n)/q)/lam := by
  have hh := history_prefix_log_bound n i q lam p raw r hi hq hbirth hp hr hsurvive hstep
  have ht : Real.log (raw n) ≤ 0 := Real.log_nonpos (hr n (le_refl _)).le hterminal
  apply (le_div_iff₀ hlam).mpr
  nlinarith

end Paper254
#print axioms Paper254.history_prefix_overhead
