import SparseDrawdown254
import IntervalTools254

noncomputable section
namespace Paper254

def masterOverhead (T K : ℕ) (lam : ℝ) : ℝ := Real.log ((T+1 : ℝ)*(K+1 : ℝ))/lam

theorem masterOverhead_nonneg (T K : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ masterOverhead T K lam := by
  unfold masterOverhead
  apply div_nonneg _ hlam.le
  apply Real.log_nonneg
  have ht := Nat.cast_nonneg T (α := ℝ)
  have hk := Nat.cast_nonneg K (α := ℝ)
  nlinarith [mul_nonneg ht hk]

theorem birthBudget_nonneg (d : ℕ) (D q : ℝ) (hD : 0 < D) (hq : 0 < q) :
    0 ≤ birthBudget d D q := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hq (sq_pos_of_pos hD))
  have hm := mul_nonneg (Nat.cast_nonneg d (α := ℝ))
    (show 0 ≤ q/D^2-1-Real.log (q/D^2) by linarith)
  unfold birthBudget
  linarith

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

theorem sparseHistory_prefix_uniform (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (e : HistoryExpert T K) (n : ℕ) (hnT : e.1.val+n < T)
    (hactive : HistoryActive (e.1.val+n+1) (expertBirth e)) :
    intervalCharge (actualMasterDifference W hD hG hη w0 q hq f e) e.1.val (n+1) ≤
      masterOverhead T K (curvature D G η/2) := by
  have hh := sparseHistory_prefix W hD hG hη w0 q hq f hf e n hnT hactive
  have he : (((e.1.val : ℝ)+1+n)/(1/(K+1 : ℝ))) =
      ((e.1.val : ℝ)+1+n)*(K+1 : ℝ) := by simp
  rw [he] at hh
  have htime : (e.1.val : ℝ)+1+n ≤ (T+1 : ℝ) := by
    exact_mod_cast (show e.1.val+1+n ≤ T+1 by omega)
  have hlog := Real.log_le_log (by positivity : 0 < ((e.1.val : ℝ)+1+n)*(K+1 : ℝ))
    (mul_le_mul_of_nonneg_right htime (by positivity : 0 ≤ (K+1 : ℝ)))
  exact le_trans hh (div_le_div_of_nonneg_right hlog
    (div_pos (curvature_pos D G η hD hG hη) (by norm_num)).le)

theorem actualComparator_interval_split (e : HistoryExpert T K) (u : ℕ → W.carrier) (a n : ℕ) :
    intervalCharge (actualComparatorDifference (T := T) W hD hG hη w0 q hq f e.2 u) a n =
      intervalCharge (actualMasterDifference W hD hG hη w0 q hq f e) a n+
        intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) a n := by
  simp_rw [intervalCharge, comparator_difference_split, Finset.sum_add_distrib]

end Trajectory
end Paper254
#print axioms Paper254.sparseHistory_prefix_uniform
