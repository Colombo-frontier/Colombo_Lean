import SparsePrefix254
import Threshold254

noncomputable section
open scoped BigOperators
namespace Paper254

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "S" => sparseTrajectory (T := T) W hD hG hη w0 q hq f
local notation "g" => actualSparseGradient (T := T) W hD hG hη w0 q hq f

def actualHistoryDifference (e : HistoryExpert T K) (u : ℕ → W.carrier) (t : ℕ) : ℝ :=
  coordinateSurrogate (curvature D G η) (g t) (S t).prediction.val ((S t).histories e).mean-
    smoothedCoordinateSurrogate (curvature D G η) (q e.2) (g t) (S t).prediction.val (u t).val

def actualComparatorDifference (k : Fin (K+1)) (u : ℕ → W.carrier) (t : ℕ) : ℝ :=
  actualSparseSurrogate (T := T) W hD hG hη w0 q hq f t (S t).prediction.val-
    smoothedCoordinateSurrogate (curvature D G η) (q k) (g t) (S t).prediction.val (u t).val

theorem comparator_difference_split (e : HistoryExpert T K) (u : ℕ → W.carrier) (t : ℕ) :
    actualComparatorDifference (T := T) W hD hG hη w0 q hq f e.2 u t =
      actualMasterDifference W hD hG hη w0 q hq f e t+
        actualHistoryDifference W hD hG hη w0 q hq f e u t := by
  unfold actualComparatorDifference actualMasterDifference actualHistoryDifference
  rw [coordinate_surrogate_toLp]
  dsimp [actualSparseSurrogate, SparseMasterState.expertPrediction]
  ring

theorem sparseHistory_drawdown (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (e : HistoryExpert T K) (u : ℕ → W.carrier) (n : ℕ) (H : ℝ)
    (hnT : e.1.val+n < T) (hactive : HistoryActive (e.1.val+n+1) (expertBirth e))
    (hdraw : ∀ j ≤ n+1,
      -H ≤ intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) e.1.val j) :
    intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) e.1.val (n+1) ≤
      (Real.sqrt (birthBudget d D (q e.2)+(curvature D G η/2)*H)+
        intervalCharge (fun t => ‖(u (t+1)).val-(u t).val‖) e.1.val n/
          (Real.sqrt 2*Real.sqrt (q e.2)))^2/(curvature D G η/2)-H := by
  let lam := curvature D G η/2
  have hlam : 0 < lam := div_pos (curvature_pos D G η hD hG hη) (by norm_num)
  let P := gaussianHistory W hD w0 lam (q e.2) hlam.le (hq e.2)
    (fun j => g (e.1.val+j)) (fun j => (S (e.1.val+j)).prediction)
  let r := fun j => coordinateSurrogate (curvature D G η) (g (e.1.val+j))
    (S (e.1.val+j)).prediction.val (P j).mean-
      smoothedCoordinateSurrogate (curvature D G η) (q e.2) (g (e.1.val+j))
        (S (e.1.val+j)).prediction.val (u (e.1.val+j)).val
  have hr (j : ℕ) (hj : j ≤ n) : r j =
      actualHistoryDifference W hD hG hη w0 q hq f e u (e.1.val+j) := by
    have ha : HistoryActive (e.1.val+j+1) (expertBirth e) :=
      historyActive_prefix hactive (by dsimp [expertBirth]; omega) (by omega)
    have hid := sparseHistory_identification W hD hG hη w0 q hq f e j (by omega) ha
    change (S (e.1.val+j)).histories e = P j at hid
    dsimp [r, actualHistoryDifference]
    rw [← hid]
  have heq (k : ℕ) (hk : k ≤ n+1) : cumulative r k =
      intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) e.1.val k := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hr j (by have hh := Finset.mem_range.mp hj; omega)
  have hg (j : ℕ) (hj : j ≤ n) : ‖g (e.1.val+j)‖ ≤ G :=
    (selectedGradient_spec W (hf _ (by omega)) (S (e.1.val+j)).prediction).2
  have hd : ∀ k ≤ n+1, -H ≤ cumulative r k := by
    intro k hk
    rw [heq k hk]
    exact hdraw k hk
  have hh := gaussianHistory_drawdown W hD hG hη w0 (q e.2) (hq e.2)
    (fun j => g (e.1.val+j)) (fun j => (S (e.1.val+j)).prediction)
    (fun j => u (e.1.val+j)) n H hg hd
  change cumulative r (n+1) ≤ _ at hh
  rw [heq (n+1) le_rfl] at hh
  exact hh

end Trajectory
end Paper254
#print axioms Paper254.sparseHistory_drawdown
