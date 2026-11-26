import Energy254
import VariationPartition254
import Mathlib.Algebra.BigOperators.Field

noncomputable section
open scoped BigOperators
namespace Paper254

def errorCorrected (r e : ℕ → ℝ) (lam : ℝ) (t : ℕ) : ℝ := r t-e t/lam

theorem corrected_cumulative (r e : ℕ → ℝ) (lam : ℝ) (n : ℕ) :
    cumulative (errorCorrected r e lam) n = cumulative r n-cumulative e n/lam := by
  simp only [cumulative,errorCorrected,Finset.sum_sub_distrib,Finset.sum_div]

theorem corrected_interval (r e : ℕ → ℝ) (lam : ℝ) (a n : ℕ) :
    intervalCharge (errorCorrected r e lam) a n = intervalCharge r a n-intervalCharge e a n/lam := by
  simp only [intervalCharge,errorCorrected,Finset.sum_sub_distrib,Finset.sum_div]

theorem robust_drawdown_bound
    (n : ℕ) (r e pre post delta : ℕ → ℝ) (lam H B : ℝ)
    (hlam : 0 < lam)
    (hpre : ∀ t ≤ n, 0 ≤ pre t) (hpost : ∀ t ≤ n, 0 ≤ post t)
    (hdelta : ∀ t < n, 0 ≤ delta t) (hinit : pre 0 ≤ B)
    (hdraw : ∀ k ≤ n+1, -H ≤ cumulative r k-cumulative e k/lam)
    (hstep : ∀ t ≤ n, lam*r t ≤ pre t-post t+e t)
    (hmove : ∀ t < n, Real.sqrt (pre (t+1)) ≤ Real.sqrt (post t)+delta t) :
    cumulative r (n+1) ≤
      (Real.sqrt (B+lam*H)+∑ t ∈ Finset.range n,delta t)^2/lam-H+cumulative e (n+1)/lam := by
  have hh := shifted_drawdown_bound n (errorCorrected r e lam) pre post delta lam H B hlam
    hpre hpost hdelta hinit
    (by intro k hk; rw [corrected_cumulative]; exact hdraw k hk)
    (by
      intro t ht
      exact Audit254.error_adjustment lam (r t) (e t) (pre t) (post t) hlam (hstep t ht)) hmove
  rw [corrected_cumulative] at hh
  linarith

theorem robust_variation_partition (r e delta : ℕ → ℝ) (T : ℕ) (C V lam : ℝ)
    (hdelta : ∀ t, 0 ≤ delta t) (hC : 0 ≤ C) (hV : 0 < V)
    (hlocal : ∀ a n, 0 < n → a+n ≤ T → intervalCharge delta a (n-1) ≤ V →
      intervalCharge r a n ≤ C+intervalCharge e a n/lam)
    (a n : ℕ) (hn : a+n ≤ T) :
    intervalCharge r a n ≤ C*(1+intervalCharge delta a (n-1)/V)+intervalCharge e a n/lam := by
  have hh := variation_partition_regret (errorCorrected r e lam) delta T C V hdelta hC hV
    (by
      intro a n hpos hend hvar
      rw [corrected_interval]
      have hl := hlocal a n hpos hend hvar
      linarith) a n hn
  rw [corrected_interval] at hh
  linarith

theorem robust_interval_restart (r e : ℕ → ℝ) (T L : ℕ) (C B lam : ℝ)
    (hC : 0 ≤ C) (hB : 2*C*L ≤ B)
    (hcase : ∀ a n, 0 < n → a+n ≤ T → ∃ k, 2*k < n ∧
      (intervalCharge r (a+k) (n-k) ≤ C+intervalCharge e (a+k) (n-k)/lam ∨
        ∃ j, 0 < j ∧ j ≤ n-k ∧ intervalCharge r (a+k) j ≤ -B+intervalCharge e (a+k) j/lam))
    (a n l : ℕ) (hn : a+n ≤ T) (hl : l ≤ L) (hsize : n < 2^l) :
    intervalCharge r a n ≤ C*l+intervalCharge e a n/lam := by
  have hh := interval_restart_bound (errorCorrected r e lam) T L C B hC hB
    (by
      intro a n hpos hend
      obtain ⟨k,hk,hgood | hbad⟩ := hcase a n hpos hend
      · refine ⟨k,hk,Or.inl ?_⟩
        rw [corrected_interval]
        linarith
      · obtain ⟨j,hj,hjn,hbad⟩ := hbad
        refine ⟨k,hk,Or.inr ⟨j,hj,hjn,?_⟩⟩
        rw [corrected_interval]
        linarith) a n l hn hl hsize
  rw [corrected_interval] at hh
  linarith

end Paper254
#print axioms Paper254.robust_interval_restart
