import SparseBudget254

noncomputable section
namespace Paper254

def restartThreshold (L a B lam : ℝ) : ℝ := 128*L*(a+B/lam)
def variationThreshold (L a B lam q : ℝ) : ℝ :=
  Real.sqrt q*Real.sqrt (B+lam*restartThreshold L a B lam)/(512*L)

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "lam" => curvature D G η/2
local notation "a₀" => masterOverhead T K lam

theorem sparse_good_suffix (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (e : HistoryExpert T K) (u : ℕ → W.carrier) (n : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hnT : e.1.val+n < T) (hactive : HistoryActive (e.1.val+n+1) (expertBirth e))
    (hvar : intervalCharge (fun t => ‖(u (t+1)).val-(u t).val‖) e.1.val n ≤
      variationThreshold L a₀ (birthBudget d D (q e.2)) lam (q e.2))
    (hdraw : ∀ j ≤ n+1,
      -restartThreshold L a₀ (birthBudget d D (q e.2)) lam ≤
        intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) e.1.val j) :
    intervalCharge (actualComparatorDifference (T := T) W hD hG hη w0 q hq f e.2 u)
      e.1.val (n+1) ≤ restartThreshold L a₀ (birthBudget d D (q e.2)) lam/(64*L) := by
  let B := birthBudget d D (q e.2)
  let H := restartThreshold L a₀ B lam
  let P := intervalCharge (fun t => ‖(u (t+1)).val-(u t).val‖) e.1.val n
  let z := P/(Real.sqrt 2*Real.sqrt (q e.2))
  have hlam : 0 < lam := div_pos (curvature_pos D G η hD hG hη) (by norm_num)
  have ha := masterOverhead_nonneg T K lam hlam
  have hB : 0 ≤ B := birthBudget_nonneg d D (q e.2) hD (hq e.2)
  have hH : 0 ≤ H := by dsimp [H, restartThreshold]; positivity
  have hC : 0 ≤ B+lam*H := by positivity
  have hP : 0 ≤ P := intervalCharge_nonneg _ (fun _ => norm_nonneg _) _ _
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hsmall : z ≤ Real.sqrt (B+lam*H)/(512*L) :=
    variation_threshold_movement (q e.2) (B+lam*H) L P (hq e.2) hC (by linarith) hP hvar
  have hgood := good_history_budget a₀ B lam L z ha hB hlam hL hz hsmall
  have hmaster := sparseHistory_prefix_uniform W hD hG hη w0 q hq f hf e n hnT hactive
  have hhistory := sparseHistory_drawdown W hD hG hη w0 q hq f hf e u n H hnT hactive hdraw
  rw [actualComparator_interval_split W hD hG hη w0 q hq f e u]
  change _ ≤ H/(64*L)
  change _ ≤ (Real.sqrt (B+lam*H)+z)^2/lam-H at hhistory
  change a₀+(Real.sqrt (B+lam*H)+z)^2/lam-H ≤ H/(64*L) at hgood
  linarith

theorem sparse_bad_prefix (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (e : HistoryExpert T K) (u : ℕ → W.carrier) (j : ℕ) (H : ℝ) (hj : 0 < j)
    (hnT : e.1.val+j ≤ T) (hactive : HistoryActive (e.1.val+j) (expertBirth e))
    (hbad : intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) e.1.val j ≤ -H) :
    intervalCharge (actualComparatorDifference (T := T) W hD hG hη w0 q hq f e.2 u)
      e.1.val j ≤ a₀-H := by
  have he : j-1+1 = j := by omega
  have ha : HistoryActive (e.1.val+(j-1)+1) (expertBirth e) := by
    convert hactive using 1 <;> omega
  have hm := sparseHistory_prefix_uniform W hD hG hη w0 q hq f hf e (j-1) (by omega) ha
  rw [he] at hm
  rw [actualComparator_interval_split W hD hG hη w0 q hq f e u]
  linarith

end Trajectory
end Paper254
#print axioms Paper254.sparse_good_suffix
#print axioms Paper254.sparse_bad_prefix
