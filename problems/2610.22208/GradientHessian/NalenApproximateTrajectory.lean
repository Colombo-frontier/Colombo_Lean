import GradientHessian.NalenPolicyOutput
import GradientHessian.NalenTuning

/-! Actual NALEN execution with arbitrary virtual snapshot replies.
Only ordinary replies are the true first jet. Snapshot symmetry and
approximation are separate pointwise properties of the decoded operator. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen Set Metric
open scoped InnerProductSpace

variable {d : ℕ} {D : ℝ} (hD : 0 ≤ D) (η : ℝ) (m q : ℕ)
  (f : Point d → ℝ) (rich : Point d → RichReply d)

def virtualIterates : Nalen.Iterates (Point d) := iterates hD η m q (ordinaryOracle f) rich

@[simp] theorem virtualIterates_initial : (virtualIterates hD η m q f rich).x 0=0 := rfl

theorem virtualIterates_delta_step (n : ℕ) :
    (virtualIterates hD η m q f rich).δ (n+1)=quadraticBorelStep hD
      (gradient f ((virtualIterates hD η m q f rich).extrapolated n),
        (virtualIterates hD η m q f rich).B n,(virtualIterates hD η m q f rich).δ n,
        (virtualIterates hD η m q f rich).v n,η) :=
  cycle_delta hD η m q (ordinaryOracle f) rich n _

theorem virtualIterates_x_step (n : ℕ) :
    (virtualIterates hD η m q f rich).x (n+1)=
      (virtualIterates hD η m q f rich).x n+(virtualIterates hD η m q f rich).δ (n+1) :=
  cycle_position hD η m q (ordinaryOracle f) rich n _

theorem virtualIterates_v_step (n : ℕ) :
    (virtualIterates hD η m q f rich).v (n+1)=quadraticBorelStep hD
      (gradient f ((virtualIterates hD η m q f rich).queryPoint n),0,0,
        (virtualIterates hD η m q f rich).v n,η) :=
  cycle_prox hD η m q (ordinaryOracle f) rich n _

theorem virtualIterates_valid (N : ℕ) : ValidSteps f D η N (virtualIterates hD η m q f rich) := by
  constructor
  · simpa only [virtualIterates,iterates,states,initial,delta_make,readGradient_oracle,
      mem_closedBall,dist_zero_right,descentDirection] using descentDirection_norm hD (gradient f 0)
  · simpa only [virtualIterates,iterates,states,initial,prox_make,readGradient_oracle,
      mem_closedBall,dist_zero_right,descentDirection] using descentDirection_norm hD (gradient f 0)
  · intro n _
    exact virtualIterates_x_step hD η m q f rich n
  · intro n _
    rw [virtualIterates_delta_step]
    exact quadraticBorelStep_spec hD _
  · intro n _
    rw [virtualIterates_v_step]
    exact quadraticBorelStep_spec hD _

theorem virtualIterates_snapshot (hm : 0 < m) (n : ℕ) :
    (virtualIterates hD η m q f rich).B n=
      readHessian (rich ((virtualIterates hD η m q f rich).extrapolated (snapshotIndex m n))) := by
  induction n with
  | zero => simp [virtualIterates,iterates,refresh,snapshotIndex,Nalen.Iterates.extrapolated]
  | succ n ih =>
    by_cases hz : (n+1)%m=0
    · simp [virtualIterates,iterates,refresh,hz,snapshotIndex,Nalen.Iterates.extrapolated]
    · change matrix (refresh m rich (n+1) (states hD η m q (ordinaryOracle f) rich (n+1)))=_
      rw [refresh,if_neg hz,states,cycle_matrix,snapshotIndex_succ_of_nonzero m n hm hz]
      exact ih

theorem virtualIterates_symmetric (hm : 0 < m)
    (hrich : ∀ z x y,⟪readHessian (rich z) x,y⟫_ℝ=⟪x,readHessian (rich z) y⟫_ℝ)
    (n : ℕ) (x y : Point d) :
    ⟪(virtualIterates hD η m q f rich).B n x,y⟫_ℝ=
      ⟪x,(virtualIterates hD η m q f rich).B n y⟫_ℝ := by
  rw [virtualIterates_snapshot hD η m q f rich hm n]
  exact hrich _ x y

theorem virtualIterates_snapshot_error (hm : 0 < m)
    (hrich : ∀ z,‖readHessian (rich z)-hessianOperator f z‖ ≤ (m : ℝ)*D) (n : ℕ) :
    ‖(virtualIterates hD η m q f rich).B n-
      hessianOperator f ((virtualIterates hD η m q f rich).extrapolated (snapshotIndex m n))‖ ≤ (m : ℝ)*D := by
  rw [virtualIterates_snapshot hD η m q f rich hm n]
  exact hrich _

theorem virtual_score_states_correct (n : ℕ) :
    score (states hD η m q (ordinaryOracle f) rich n)=
      ‖gradient f (best (states hD η m q (ordinaryOracle f) rich n))‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi : score (beforeCandidate hD η m q (ordinaryOracle f) rich n)=
        ‖gradient f (best (beforeCandidate hD η m q (ordinaryOracle f) rich n))‖ := by
      rw [score_beforeCandidate,best_beforeCandidate]
      exact ih
    change score (candidateCheck q (ordinaryOracle f) n (beforeCandidate hD η m q (ordinaryOracle f) rich n))=_
    change _=‖gradient f (best (candidateCheck q (ordinaryOracle f) n (beforeCandidate hD η m q (ordinaryOracle f) rich n)))‖
    unfold candidateCheck
    split_ifs
    · rw [readGradient_oracle]
      unfold consider
      split_ifs
      · rfl
      · exact hi
    · exact hi

theorem virtual_score_completed_block_le (hq : 0 < q) (k : ℕ) :
    score (states hD η m q (ordinaryOracle f) rich ((k+1)*q)) ≤
      ‖gradient f ((virtualIterates hD η m q f rich).candidate q k)‖ := by
  let n := (k+1)*q-1
  have hn : n+1=(k+1)*q := by
    change (k+1)*q-1+1=(k+1)*q
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos k) hq))
  have hz : (n+1)%q=0 := by rw [hn]; simp
  have ha : average q n (beforeCandidate hD η m q (ordinaryOracle f) rich n)=
      (virtualIterates hD η m q f rich).candidate q k := by
    rw [average_beforeCandidate,hn]
    exact average_completed_block hD η m q (ordinaryOracle f) rich hq k
  rw [← hn]
  change score (candidateCheck q (ordinaryOracle f) n (beforeCandidate hD η m q (ordinaryOracle f) rich n))≤_
  rw [candidateCheck,if_pos hz,readGradient_oracle]
  exact (score_consider_le_norm q n _ _).trans_eq (congrArg (fun x => ‖gradient f x‖) ha)

theorem virtual_output_gradient_le_candidate (hq : 0 < q) (N k : ℕ) (hk : (k+1)*q ≤ N)
    (seed : PUnit) :
    ‖gradient f ((policy d hD η m q N).output
      ((policy d hD η m q N).run (ordinaryOracle f) rich (1+4*N) seed))‖ ≤
        ‖gradient f ((virtualIterates hD η m q f rich).candidate q k)‖ := by
  rw [machine_output,← virtual_score_states_correct]
  exact (score_states_antitone hD η m q (ordinaryOracle f) rich hk).trans
    (virtual_score_completed_block_le hD η m q f rich hq k)

theorem virtual_tuned_output_stationary {T : ℝ} (hf : Model.Admissible T f)
    (hm : 1 ≤ m) (hq : 1 ≤ q) (K N : ℕ) (hK : 1 ≤ K) (hmq : m ≤ q^3)
    (hKq : K*q ≤ N) (hTK : 256*T ≤ (K : ℝ))
    (hrichSym : ∀ z x y,⟪readHessian (rich z) x,y⟫_ℝ=⟪x,readHessian (rich z) y⟫_ℝ)
    (hrichError : ∀ z,‖readHessian (rich z)-hessianOperator f z‖ ≤ (m : ℝ)*stepRadius q)
    (seed : PUnit) :
    ‖gradient f ((policy d (stepRadius_pos hq).le (stepSize m q) m q N).output
      ((policy d (stepRadius_pos hq).le (stepSize m q) m q N).run
        (ordinaryOracle f) rich (1+4*N) seed))‖ ≤ 1 := by
  refine Nalen.output_stationary
    (virtualIterates_valid (stepRadius_pos hq).le (stepSize m q) m q f rich N)
    hf.smooth hf.hessianLip hm hq hK hmq hKq
    (fun n _ => virtualIterates_symmetric (stepRadius_pos hq).le (stepSize m q) m q f rich
      (by omega) hrichSym n)
    (fun n _ => virtualIterates_snapshot_error (stepRadius_pos hq).le (stepSize m q) m q f rich
      (by omega) hrichError n) _ ?_ hf.boundedBelow ?_ hTK
  · intro k hk
    apply virtual_output_gradient_le_candidate (stepRadius_pos hq).le (stepSize m q) m q f rich
      (by omega) N k _ seed
    exact (Nat.mul_le_mul_right q (Nat.succ_le_of_lt hk)).trans hKq
  · simpa only [virtualIterates_initial] using hf.gap

end GradientHessian.NalenPolicy
