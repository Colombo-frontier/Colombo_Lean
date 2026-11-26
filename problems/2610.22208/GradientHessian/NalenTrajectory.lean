import GradientHessian.NalenSubproblem
import GradientHessian.NalenTrajectoryGeometry
import GradientHessian.NalenObjective

/-! Literal finite-prefix NALEN updates. Validity contains only the
actual minimization problems and state updates, never a regret or
convergence estimate. -/

noncomputable section
namespace GradientHessian.Nalen
open Set Metric
open scoped InnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Iterates where
  x : ℕ → E
  δ : ℕ → E
  v : ℕ → E
  B : ℕ → E →L[ℝ] E

variable {E}

def Iterates.extrapolated (s : Iterates E) (n : ℕ) : E := midpoint (s.x n) (s.δ n)
def Iterates.queryPoint (s : Iterates E) (n : ℕ) : E := midpoint (s.x n) (s.δ (n+1))
def Iterates.candidate (s : Iterates E) (q k : ℕ) : E :=
  ((q : ℝ)⁻¹) • ∑ j ∈ Finset.range q,s.queryPoint (k*q+j)

variable [CompleteSpace E]

structure ValidSteps (f : E → ℝ) (D η : ℝ) (N : ℕ) (s : Iterates E) : Prop where
  initial_delta : s.δ 0 ∈ closedBall (0 : E) D
  initial_v : s.v 0 ∈ closedBall (0 : E) D
  x_step : ∀ n < N,s.x (n+1)=s.x n+s.δ (n+1)
  delta_step : ∀ n < N,s.δ (n+1) ∈ closedBall (0 : E) D ∧
    IsMinOn (quadraticModel (gradient f (s.extrapolated n)) (s.B n) (s.δ n) (s.v n) η)
      (closedBall (0 : E) D) (s.δ (n+1))
  v_step : ∀ n < N,s.v (n+1) ∈ closedBall (0 : E) D ∧
    IsMinOn (quadraticModel (gradient f (s.queryPoint n)) 0 0 (s.v n) η)
      (closedBall (0 : E) D) (s.v (n+1))

theorem ValidSteps.delta_norm {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (n : ℕ) (hn : n ≤ N) : ‖s.δ n‖ ≤ D := by
  cases n with
  | zero => simpa only [mem_closedBall,dist_zero_right] using hs.initial_delta
  | succ n => simpa only [mem_closedBall,dist_zero_right] using (hs.delta_step n (by omega)).1

theorem ValidSteps.v_norm {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (n : ℕ) (hn : n ≤ N) : ‖s.v n‖ ≤ D := by
  cases n with
  | zero => simpa only [mem_closedBall,dist_zero_right] using hs.initial_v
  | succ n => simpa only [mem_closedBall,dist_zero_right] using (hs.v_step n (by omega)).1

theorem ValidSteps.radius_nonneg {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) : 0 ≤ D :=
  (norm_nonneg (s.δ 0)).trans (hs.delta_norm 0 (Nat.zero_le _))

theorem ValidSteps.displacement {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (p r : ℕ) (hpr : p+r ≤ N) :
    ‖s.x (p+r)-s.x p‖ ≤ (r : ℝ)*D := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hn : p+r < N := by omega
    calc
      ‖s.x (p+(r+1))-s.x p‖ ≤ ‖s.x (p+r+1)-s.x (p+r)‖+‖s.x (p+r)-s.x p‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖s.δ (p+r+1)‖+‖s.x (p+r)-s.x p‖ := by rw [hs.x_step _ hn]; simp
      _ ≤ D+(r : ℝ)*D := add_le_add (hs.delta_norm _ (by omega)) (ih (by omega))
      _ = ((r+1 : ℕ) : ℝ)*D := by push_cast; ring

theorem ValidSteps.snapshot_distance {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : n ≤ N) :
    ‖s.extrapolated (snapshotIndex m n)-s.extrapolated n‖ ≤ (m : ℝ)*D := by
  have hp : snapshotIndex m n+n%m=n := Nat.sub_add_cancel (Nat.mod_le n m)
  have hpn : snapshotIndex m n ≤ N := (Nat.sub_le _ _).trans hn
  have hd := hs.displacement (snapshotIndex m n) (n%m) (by rw [hp]; exact hn)
  rw [hp,norm_sub_rev] at hd
  have he : ‖s.δ (snapshotIndex m n)-s.δ n‖ ≤ 2*D :=
    (norm_sub_le _ _).trans (by linarith [hs.delta_norm _ hpn,hs.delta_norm n hn])
  have hh := norm_midpoint_sub (s.x (snapshotIndex m n)) (s.x n)
    (s.δ (snapshotIndex m n)) (s.δ n)
  have hmod : ((n%m : ℕ) : ℝ)+1 ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt n (by omega))
  have hb := mul_le_mul_of_nonneg_right hmod hs.radius_nonneg
  change ‖midpoint _ _-midpoint _ _‖ ≤ _
  nlinarith only [hd,he,hh,hb]

end GradientHessian.Nalen
