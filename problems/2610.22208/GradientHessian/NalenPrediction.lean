import GradientHessian.NalenTrajectory
import GradientHessian.NalenRegret

/-! The actual NALEN hint error and block regret, including approximate
snapshot Hessians. Every estimate follows from the literal minimization
updates and the objective's Lipschitz Hessian. -/

noncomputable section
namespace GradientHessian.Nalen
open Set Metric
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def Iterates.prediction (s : Iterates E) (f : E → ℝ) (n : ℕ) : E :=
  gradient f (s.extrapolated n)+(1/2 : ℝ) • s.B n (s.δ (n+1)-s.δ n)

theorem ValidSteps.prediction_error {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (hn : n < N)
    (hB : ‖s.B n-hessianOperator f (s.extrapolated (snapshotIndex m n))‖ ≤ (m : ℝ)*D) :
    ‖s.prediction f n-gradient f (s.queryPoint n)‖ ≤
      (2*(m : ℝ)*D)*‖s.δ (n+1)-s.δ n‖ := by
  have hD := hs.radius_nonneg
  have hd := prediction_displacement (s.x n) (s.δ (n+1)) (s.δ n)
    (hs.delta_norm _ (by omega)) (hs.delta_norm _ (by omega))
  have hz := hs.snapshot_distance m hm n (by omega)
  have ht := objective_prediction_remainder hf hL (s.B n) (s.extrapolated n)
    (s.queryPoint n) (s.extrapolated (snapshotIndex m n)) hB
  simp only [NNReal.coe_one,one_mul] at ht
  have hP : gradient f (s.extrapolated n)+s.B n (s.queryPoint n-s.extrapolated n)=s.prediction f n := by
    simp only [Iterates.queryPoint,Iterates.extrapolated,midpoint_sub,map_smul,Iterates.prediction]
  rw [hP] at ht
  have hd' : ‖s.queryPoint n-s.extrapolated n‖ ≤ D := hd.2
  have hdEq : ‖s.queryPoint n-s.extrapolated n‖=(1/2 : ℝ)*‖s.δ (n+1)-s.δ n‖ := hd.1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmd : D ≤ (m : ℝ)*D := by nlinarith [hs.radius_nonneg]
  calc
    ‖s.prediction f n-gradient f (s.queryPoint n)‖ ≤
        (‖s.queryPoint n-s.extrapolated n‖+
          ‖s.extrapolated (snapshotIndex m n)-s.extrapolated n‖+(m : ℝ)*D)*
          ‖s.queryPoint n-s.extrapolated n‖ := ht
    _ ≤ (4*(m : ℝ)*D)*‖s.queryPoint n-s.extrapolated n‖ :=
      mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    _ = _ := by rw [hdEq]; ring

theorem ValidSteps.block_regret {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) (m : ℕ) (hm : 1 ≤ m)
    (hη : 0 < η) (hstep : 8*η^2*(2*(m : ℝ)*D)^2 ≤ 1)
    (hBsym : ∀ n < N,∀ u v,⟪s.B n u,v⟫_ℝ=⟪u,s.B n v⟫_ℝ)
    (hB : ∀ n < N,‖s.B n-hessianOperator f (s.extrapolated (snapshotIndex m n))‖ ≤ (m : ℝ)*D)
    (p q : ℕ) (hpq : p+q ≤ N) (u : E) (hu : ‖u‖ ≤ D) :
    ∑ n ∈ Finset.range q,⟪gradient f (s.queryPoint (p+n)),s.δ (p+n+1)-u⟫_ℝ ≤ 3*D^2/η := by
  have hD := hs.radius_nonneg
  let δ' (n : ℕ) := s.δ (min (p+n) N)
  let v' (n : ℕ) := s.v (min (p+n) N)
  have hδ' (n : ℕ) : ‖δ' n‖ ≤ D := hs.delta_norm _ (Nat.min_le_right _ _)
  have hv' (n : ℕ) : ‖v' n‖ ≤ D := hs.v_norm _ (Nat.min_le_right _ _)
  have hh (n : ℕ) (hn : n < q) :
      0 ≤ ⟪η • s.prediction f (p+n)+δ' (n+1)-v' n,v' (n+1)-δ' (n+1)⟫_ℝ := by
    have hpn : p+n < N := by omega
    have hnext : p+(n+1) ≤ N := by omega
    simp only [δ',v',min_eq_left hnext,min_eq_left hpn.le,Nat.add_assoc]
    exact quadraticModel_variational hη (gradient f (s.extrapolated (p+n))) (s.B (p+n))
      (s.δ (p+n)) (s.v (p+n)) (s.δ (p+n+1)) (hBsym _ hpn)
      (hs.delta_step _ hpn).1 (hs.delta_step _ hpn).2 (hs.v_step _ hpn).1
  have hg (n : ℕ) (hn : n < q) :
      0 ≤ ⟪η • gradient f (s.queryPoint (p+n))+v' (n+1)-v' n,u-v' (n+1)⟫_ℝ := by
    have hpn : p+n < N := by omega
    have hnext : p+(n+1) ≤ N := by omega
    simp only [v',min_eq_left hnext,min_eq_left hpn.le,Nat.add_assoc]
    exact proximalModel_variational hη _ _ _ (hs.v_step _ hpn).1 (hs.v_step _ hpn).2
      (by simpa only [mem_closedBall,dist_zero_right] using hu)
  have herr (n : ℕ) (hn : n < q) :
      ‖s.prediction f (p+n)-gradient f (s.queryPoint (p+n))‖ ≤
        (2*(m : ℝ)*D)*‖δ' (n+1)-δ' n‖ := by
    have hpn : p+n < N := by omega
    have hnext : p+(n+1) ≤ N := by omega
    simp only [δ',min_eq_left hnext,min_eq_left hpn.le,Nat.add_assoc]
    exact hs.prediction_error hf hL m hm _ hpn (hB _ hpn)
  have h := extragradient_block_regret hη (show 0 ≤ 2*(m : ℝ)*D by positivity)
    hstep q (fun n => gradient f (s.queryPoint (p+n))) (fun n => s.prediction f (p+n))
    δ' v' u hu hδ' hv' hh hg herr
  have he : (∑ n ∈ Finset.range q,⟪gradient f (s.queryPoint (p+n)),δ' (n+1)-u⟫_ℝ)=
      ∑ n ∈ Finset.range q,⟪gradient f (s.queryPoint (p+n)),s.δ (p+n+1)-u⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    simp only [δ',min_eq_left (show p+(n+1) ≤ N by omega),Nat.add_assoc]
  rwa [he] at h

end GradientHessian.Nalen
