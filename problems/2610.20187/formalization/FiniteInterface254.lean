import SparseTrajectory254
import IntervalTools254
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open scoped BigOperators
namespace Paper254

def extendFinite {α : Type*} {T : ℕ} (default : α) (f : Fin T → α) (n : ℕ) : α :=
  if hn : n < T then f ⟨n,hn⟩ else default

theorem extendFinite_at {α : Type*} {T : ℕ} (default : α) (f : Fin T → α) (t : Fin T) :
    extendFinite default f t.val = f t := by simp [extendFinite, t.isLt]

theorem pathLength_adjacent {d n : ℕ} {D : ℝ} {W : Domain d D}
    (u : Fin (n+1) → W.carrier) :
    pathLength u = ∑ j : Fin n, ‖(u j.succ).val-(u j.castSucc).val‖ := by
  unfold pathLength
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, lt_self_iff_false, dite_false, zero_add,
    Fin.val_succ, Nat.succ_pos, dite_true, Nat.add_sub_cancel]
  rfl

theorem pathLength_extension {d T : ℕ} {D : ℝ} {W : Domain d D}
    (w0 : W.carrier) (u : Fin T → W.carrier) :
    pathLength u = intervalCharge
      (fun t => ‖(extendFinite w0 u (t+1)).val-(extendFinite w0 u t).val‖) 0 (T-1) := by
  cases T with
  | zero => simp [pathLength, intervalCharge]
  | succ n =>
    rw [pathLength_adjacent]
    simp only [intervalCharge, Nat.add_sub_cancel, Nat.zero_add]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hj : j.val < n+1 := by omega
    have hjs : j.val+1 < n+1 := by omega
    simp only [extendFinite, dif_pos hj, dif_pos hjs]
    rfl

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k)

theorem sparseOnline_predictions (f : Fin T → Loss d) (t : Fin T) :
    predictions (sparseOnlineLearner W hD hG hη w0 q hq) f t =
      (sparseTrajectory (T := T) W hD hG hη w0 q hq (extendFinite (fun _ => 0) f) t.val).prediction := by
  let padded : ℕ → Loss d := fun n => if hn : n < t.val then past f t ⟨n,hn⟩ else fun _ => 0
  have hh := sparseTrajectory_causal (T := T) W hD hG hη w0 q hq
    padded (extendFinite (fun _ => 0) f) t.val (by
      intro n hn
      have hnT : n < T := Nat.lt_trans hn t.isLt
      simp only [padded, dif_pos hn, extendFinite, dif_pos hnT, past])
  change (sparseTrajectory (T := T) W hD hG hη w0 q hq padded t.val).prediction = _
  rw [hh]

theorem sparseOnline_regret (f : Fin T → Loss d) (u : Fin T → W.carrier) :
    regret (sparseOnlineLearner W hD hG hη w0 q hq) f u =
      intervalCharge (fun n =>
        extendFinite (fun _ => 0) f n
          (sparseTrajectory (T := T) W hD hG hη w0 q hq (extendFinite (fun _ => 0) f) n).prediction.val-
        extendFinite (fun _ => 0) f n (extendFinite w0 u n).val) 0 T := by
  simp only [regret, intervalCharge, Nat.zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  rw [sparseOnline_predictions W hD hG hη w0 q hq f t, extendFinite_at, extendFinite_at]

end Trajectory
end Paper254
#print axioms Paper254.pathLength_extension
#print axioms Paper254.sparseOnline_regret
