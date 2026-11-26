import SparseWeights254
import HistoryPrefix254
import IntervalRestart254

noncomputable section
namespace Paper254

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "S" => sparseTrajectory (T := T) W hD hG hη w0 q hq f

def actualSparseSurrogate (n : ℕ) : Loss d :=
  rankOneSurrogate (curvature D G η) (actualSparseGradient (T := T) W hD hG hη w0 q hq f n)
    (S n).prediction.val

def actualMasterDifference (e : HistoryExpert T K) (n : ℕ) : ℝ :=
  let s := actualSparseSurrogate (T := T) W hD hG hη w0 q hq f n
  s (S n).prediction.val-s ((S n).expertPrediction e).val

theorem sparseHistory_prefix (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (e : HistoryExpert T K) (n : ℕ) (hnT : e.1.val+n < T)
    (hactive : HistoryActive (e.1.val+n+1) (expertBirth e)) :
    intervalCharge (actualMasterDifference W hD hG hη w0 q hq f e) e.1.val (n+1) ≤
      Real.log (((e.1.val : ℝ)+1+n)/(1/(K+1 : ℝ)))/(curvature D G η/2) := by
  let p := fun j => (S (e.1.val+j)).weights.weight e
  let raw := fun j => ((S (e.1.val+j)).rawWeights (G := G) (η := η) (f (e.1.val+j))).weight e
  let r := fun j => actualMasterDifference W hD hG hη w0 q hq f e (e.1.val+j)
  have hlam : 0 < curvature D G η/2 := div_pos (curvature_pos D G η hD hG hη) (by norm_num)
  have hborn : (1/(K+1 : ℝ))/(e.1.val+1 : ℝ) ≤ p 0 := by
    simpa [p] using sparseHistory_birth_weight W hD hG hη w0 q hq f e
  have hact (j : ℕ) (hj : j ≤ n) : HistoryActive (e.1.val+j+1) (expertBirth e) :=
    historyActive_prefix hactive (by dsimp [expertBirth]; omega) (by omega)
  have hp (j : ℕ) (hj : j ≤ n) : 0 < p j :=
    sparseHistory_weight_positive W hD hG hη w0 q hq f e (e.1.val+j)
      (by omega) (by omega) (hact j hj)
  have hraw (j : ℕ) (hj : j ≤ n) : 0 < raw j :=
    (S (e.1.val+j)).raw_weight_pos (G := G) (η := η) (f (e.1.val+j)) e (hp j hj)
  have hsurv (j : ℕ) (hj : j < n) :
      ((e.1.val+1 : ℝ)+j)/((e.1.val+1 : ℝ)+j+1)*raw j ≤ p (j+1) := by
    have ha : HistoryActive (e.1.val+j+2) (expertBirth e) :=
      historyActive_prefix hactive (by dsimp [expertBirth]; omega) (by omega)
    have hh := sparseHistory_survival W hD hG hη w0 q hq f e (e.1.val+j) (by omega) ha
    convert hh using 1 <;> dsimp [p, raw] <;> push_cast <;> ring
  have hstep (j : ℕ) (hj : j ≤ n) :
      (curvature D G η/2)*r j ≤ Real.log (raw j)-Real.log (p j) :=
    (S (e.1.val+j)).exponential_comparison hD hG hη (f (e.1.val+j))
      (hf _ (by omega)) e (hp j hj)
  have ht : raw n ≤ 1 := ((S (e.1.val+n)).rawWeights (G := G) (η := η) (f (e.1.val+n))).weight_le_one e
  exact history_prefix_overhead n (e.1.val+1 : ℝ) (1/(K+1 : ℝ)) (curvature D G η/2)
    p raw r (by positivity) (by positivity) hlam hborn hp hraw hsurv hstep ht

end Trajectory
end Paper254
#print axioms Paper254.sparseHistory_prefix
