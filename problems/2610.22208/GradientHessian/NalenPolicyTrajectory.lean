import GradientHessian.NalenPolicyExecution

/-! The actual compiled trajectory satisfies the exact minimization
updates and uses the actual Hessian at its most recent scheduled snapshot. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen Set Metric
open scoped InnerProductSpace

variable {d : ℕ} {D : ℝ} (hD : 0≤D) (η : ℝ) (m q : ℕ) (f : Point d → ℝ)

def actualIterates : Nalen.Iterates (Point d) :=
  iterates hD η m q (ordinaryOracle f) (richOracle f)

@[simp] theorem actualIterates_initial : (actualIterates hD η m q f).x 0=0 := rfl

theorem actualIterates_delta_step (n : ℕ) :
    (actualIterates hD η m q f).δ (n+1)=quadraticBorelStep hD
      (gradient f ((actualIterates hD η m q f).extrapolated n),
        (actualIterates hD η m q f).B n,(actualIterates hD η m q f).δ n,
        (actualIterates hD η m q f).v n,η) := by
  exact cycle_delta hD η m q (ordinaryOracle f) (richOracle f) n _

theorem actualIterates_x_step (n : ℕ) :
    (actualIterates hD η m q f).x (n+1)=
      (actualIterates hD η m q f).x n+(actualIterates hD η m q f).δ (n+1) :=
  cycle_position hD η m q (ordinaryOracle f) (richOracle f) n _

theorem actualIterates_v_step (n : ℕ) :
    (actualIterates hD η m q f).v (n+1)=quadraticBorelStep hD
      (gradient f ((actualIterates hD η m q f).queryPoint n),0,0,(actualIterates hD η m q f).v n,η) :=
  cycle_prox hD η m q (ordinaryOracle f) (richOracle f) n _

theorem actualIterates_valid (N : ℕ) : ValidSteps f D η N (actualIterates hD η m q f) := by
  constructor
  · simpa only [actualIterates,iterates,states,initial,delta_make,readGradient_oracle,
      mem_closedBall,dist_zero_right,descentDirection] using descentDirection_norm hD (gradient f 0)
  · simpa only [actualIterates,iterates,states,initial,prox_make,readGradient_oracle,
      mem_closedBall,dist_zero_right,descentDirection] using descentDirection_norm hD (gradient f 0)
  · intro n hn
    exact actualIterates_x_step hD η m q f n
  · intro n hn
    rw [actualIterates_delta_step]
    exact quadraticBorelStep_spec hD _
  · intro n hn
    rw [actualIterates_v_step]
    exact quadraticBorelStep_spec hD _

theorem snapshotIndex_succ_of_nonzero (m n : ℕ) (hm : 0<m) (hz : (n+1)%m≠0) :
    snapshotIndex m (n+1)=snapshotIndex m n := by
  have hm1 : 1<m := by
    by_cases hmEq : m=1
    · exfalso
      apply hz
      rw [hmEq,Nat.mod_one]
    · omega
  have hmod := Nat.mod_lt n hm
  have he : (n+1)%m=(n%m+1)%m := by rw [Nat.add_mod,Nat.mod_eq_of_lt hm1]
  have hlt : n%m+1<m := by
    apply lt_of_le_of_ne (Nat.succ_le_of_lt hmod)
    intro heq
    change n%m+1=m at heq
    apply hz
    rw [he,heq,Nat.mod_self]
  rw [Nat.mod_eq_of_lt hlt] at he
  unfold snapshotIndex
  omega

theorem actualIterates_snapshot (hm : 0<m) (n : ℕ) :
    (actualIterates hD η m q f).B n=
      hessianOperator f ((actualIterates hD η m q f).extrapolated (snapshotIndex m n)) := by
  induction n with
  | zero => simp [actualIterates,iterates,refresh,snapshotIndex,Nalen.Iterates.extrapolated]
  | succ n ih =>
    by_cases hz : (n+1)%m=0
    · simp [actualIterates,iterates,refresh,hz,snapshotIndex,Nalen.Iterates.extrapolated]
    · change matrix (refresh m (richOracle f) (n+1) (states hD η m q (ordinaryOracle f) (richOracle f) (n+1)))=_
      rw [refresh,if_neg hz,states,cycle_matrix]
      rw [snapshotIndex_succ_of_nonzero m n hm hz]
      exact ih

theorem actualIterates_symmetric (hm : 0<m) (hf : ContDiff ℝ 2 f) (n : ℕ) (x y : Point d) :
    ⟪(actualIterates hD η m q f).B n x,y⟫_ℝ=⟪x,(actualIterates hD η m q f).B n y⟫_ℝ := by
  rw [actualIterates_snapshot hD η m q f hm n]
  exact hessianOperator_symmetric hf _ x y

theorem actualIterates_snapshot_error (hm : 0<m) (n : ℕ) :
    ‖(actualIterates hD η m q f).B n-
      hessianOperator f ((actualIterates hD η m q f).extrapolated (snapshotIndex m n))‖≤(m:ℝ)*D := by
  rw [actualIterates_snapshot hD η m q f hm n,sub_self,norm_zero]
  positivity

end GradientHessian.NalenPolicy
