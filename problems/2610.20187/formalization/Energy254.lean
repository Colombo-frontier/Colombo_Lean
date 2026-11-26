import Audit254

/-! Full finite-sequence proof of the shifted drawdown lemma, after its
one-step and square-root movement hypotheses have been established.
This is not a claim that those hypotheses hold for an implemented Gaussian
algorithm. All hypotheses below are explicitly present in Lemma B.8's proof. -/
noncomputable section
open scoped BigOperators
namespace Paper254

def cumulative (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, r k

theorem cumulative_succ (r : ℕ → ℝ) (n : ℕ) :
    cumulative r (n+1) = cumulative r n + r n := by
  exact Finset.sum_range_succ r n

/-- n+1 rounds; delta contains precisely the n internal comparator jumps.
No upper bound on the unshifted potential is assumed. -/
theorem shifted_drawdown_bound
    (n : ℕ) (r pre post delta : ℕ → ℝ) (lam H B : ℝ)
    (hlam : 0 < lam)
    (hpre : ∀ t ≤ n, 0 ≤ pre t) (hpost : ∀ t ≤ n, 0 ≤ post t)
    (hdelta : ∀ t < n, 0 ≤ delta t)
    (hinit : pre 0 ≤ B)
    (hdraw : ∀ k ≤ n+1, -H ≤ cumulative r k)
    (hstep : ∀ t ≤ n, lam * r t ≤ pre t - post t)
    (hmove : ∀ t < n, Real.sqrt (pre (t+1)) ≤ Real.sqrt (post t) + delta t) :
    cumulative r (n+1) ≤
      (Real.sqrt (B + lam * H) + ∑ t ∈ Finset.range n, delta t)^2 / lam - H := by
  let E : ℕ → ℝ := fun t => pre t + lam * (cumulative r t + H)
  have hEnonneg : ∀ t ≤ n, 0 ≤ E t := by
    intro t ht
    have hp := hpre t ht
    have hd := hdraw t (by omega)
    dsimp [E]
    exact add_nonneg hp (mul_nonneg (le_of_lt hlam) (by linarith))
  have hpostEnergy : ∀ t ≤ n,
      post t + lam * (cumulative r (t+1) + H) ≤ E t := by
    intro t ht
    rw [cumulative_succ]
    exact Audit254.shifted_energy_step lam (r t) (cumulative r t) H
      (pre t) (post t) (hstep t ht)
  have hroot : ∀ t < n, Real.sqrt (E (t+1)) ≤ Real.sqrt (E t) + delta t := by
    intro t ht
    have hc : 0 ≤ lam * (cumulative r (t+1) + H) := by
      have hd := hdraw (t+1) (by omega)
      exact mul_nonneg (le_of_lt hlam) (by linarith)
    exact Audit254.shifted_root_step (pre (t+1)) (post t)
      (lam * (cumulative r (t+1) + H)) (delta t) (E t)
      (hpre (t+1) (by omega)) (hpost t (by omega)) hc
      (hdelta t ht) (hmove t ht) (hpostEnergy t (by omega))
  have htel := Audit254.telescope (fun t => Real.sqrt (E t)) delta n hroot
  have hEzero : E 0 ≤ B + lam * H := by
    simp only [E, cumulative, Finset.range_zero, Finset.sum_empty, zero_add]
    linarith
  have hstart := Real.sqrt_le_sqrt hEzero
  have hrootFinal : Real.sqrt (E n) ≤
      Real.sqrt (B + lam * H) + ∑ t ∈ Finset.range n, delta t := by linarith
  have hM : 0 ≤ Real.sqrt (B + lam * H) + ∑ t ∈ Finset.range n, delta t := by
    apply add_nonneg (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro t ht
    exact hdelta t (Finset.mem_range.mp ht)
  have hsq := Real.sq_sqrt (hEnonneg n (le_refl _))
  have hEbound : E n ≤
      (Real.sqrt (B + lam * H) + ∑ t ∈ Finset.range n, delta t)^2 := by
    have hn := Real.sqrt_nonneg (E n)
    nlinarith [mul_nonneg (sub_nonneg.mpr hrootFinal) (add_nonneg hM hn)]
  have hlast := hpostEnergy n (le_refl _)
  exact Audit254.drawdown_terminal lam (cumulative r (n+1)) H (post n)
    ((Real.sqrt (B + lam * H) + ∑ t ∈ Finset.range n, delta t)^2)
    hlam (hpost n (le_refl _)) (le_trans hlast hEbound)

end Paper254
#print axioms Paper254.shifted_drawdown_bound
