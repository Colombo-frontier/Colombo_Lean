import GradientHessian.NalenPolicyTrajectory

/-! Every stored complete-block candidate is the exact analytic average,
and the returned point has gradient norm no larger than every candidate.
The comparison scores are obtained by actual ordinary oracle calls. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen
open scoped BigOperators

variable {d : ℕ} {D : ℝ} (hD : 0≤D) (η : ℝ) (m q : ℕ)

def beforeCandidate (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) (n : ℕ) : Data (Point d) :=
  correction hD η ordinary n (prediction hD η ordinary
    (refresh m rich n (states hD η m q ordinary rich n)))

theorem queries_states (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d)
    (n i : ℕ) (hi : i<n) :
    queries (states hD η m q ordinary rich n) i=(iterates hD η m q ordinary rich).queryPoint i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [states,cycle_queries]
    by_cases he : i=n
    · subst i
      rw [Function.update_same]
      rfl
    · rw [Function.update_of_ne he]
      exact ih (by omega)

theorem average_completed_block (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d)
    (hq : 0<q) (k : ℕ) :
    average q ((k+1)*q-1) (states hD η m q ordinary rich ((k+1)*q))=
      (iterates hD η m q ordinary rich).candidate q k := by
  have he : (k+1)*q-1+1-q=k*q := by rw [Nat.add_mul]; simp only [one_mul]; omega
  simp only [average,he,Nalen.Iterates.candidate]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply queries_states
  have hj' := Finset.mem_range.mp hj
  rw [Nat.add_mul]
  simp only [one_mul]
  omega

theorem average_beforeCandidate (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) (n : ℕ) :
    average q n (beforeCandidate hD η m q ordinary rich n)=
      average q n (states hD η m q ordinary rich (n+1)) := by
  simp only [average,states,cycle,queries_candidateCheck,beforeCandidate]

@[simp] theorem best_refresh (m n : ℕ) (rich : Point d → RichReply d) (s : Data (Point d)) :
    best (refresh m rich n s)=best s := by
  unfold refresh
  split_ifs <;> rfl

@[simp] theorem score_refresh (m n : ℕ) (rich : Point d → RichReply d) (s : Data (Point d)) :
    score (refresh m rich n s)=score s := by
  unfold refresh
  split_ifs <;> rfl

theorem best_beforeCandidate (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) (n : ℕ) :
    best (beforeCandidate hD η m q ordinary rich n)=best (states hD η m q ordinary rich n) := by
  simp [beforeCandidate,correction,prediction,correct,predict]

theorem score_beforeCandidate (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) (n : ℕ) :
    score (beforeCandidate hD η m q ordinary rich n)=score (states hD η m q ordinary rich n) := by
  simp [beforeCandidate,correction,prediction,correct,predict]

theorem score_states_antitone (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    Antitone (fun n => score (states hD η m q ordinary rich n)) := by
  apply antitone_nat_of_succ_le
  intro n
  change score (candidateCheck q ordinary n (beforeCandidate hD η m q ordinary rich n))≤_
  rw [← score_beforeCandidate hD η m q ordinary rich n]
  unfold candidateCheck
  split_ifs
  · exact score_consider_le _ _ _ _
  · exact le_rfl

theorem score_states_correct (f : Point d → ℝ) (n : ℕ) :
    score (states hD η m q (ordinaryOracle f) (richOracle f) n)=
      ‖gradient f (best (states hD η m q (ordinaryOracle f) (richOracle f) n))‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi : score (beforeCandidate hD η m q (ordinaryOracle f) (richOracle f) n)=
        ‖gradient f (best (beforeCandidate hD η m q (ordinaryOracle f) (richOracle f) n))‖ := by
      rw [score_beforeCandidate,best_beforeCandidate]
      exact ih
    change score (candidateCheck q (ordinaryOracle f) n (beforeCandidate hD η m q (ordinaryOracle f) (richOracle f) n))=_
    change _=‖gradient f (best (candidateCheck q (ordinaryOracle f) n (beforeCandidate hD η m q (ordinaryOracle f) (richOracle f) n)))‖
    unfold candidateCheck
    split_ifs
    · rw [readGradient_oracle]
      unfold consider
      split_ifs
      · rfl
      · exact hi
    · exact hi

theorem score_completed_block_le (f : Point d → ℝ) (hq : 0<q) (k : ℕ) :
    score (states hD η m q (ordinaryOracle f) (richOracle f) ((k+1)*q))≤
      ‖gradient f ((actualIterates hD η m q f).candidate q k)‖ := by
  let n := (k+1)*q-1
  have hn : n+1=(k+1)*q := by
    change (k+1)*q-1+1=(k+1)*q
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos k) hq))
  have hz : (n+1)%q=0 := by rw [hn]; simp
  have ha : average q n (beforeCandidate hD η m q (ordinaryOracle f) (richOracle f) n)=
      (actualIterates hD η m q f).candidate q k := by
    rw [average_beforeCandidate,hn]
    exact average_completed_block hD η m q (ordinaryOracle f) (richOracle f) hq k
  rw [← hn]
  change score (candidateCheck q (ordinaryOracle f) n (beforeCandidate hD η m q (ordinaryOracle f) (richOracle f) n))≤_
  rw [candidateCheck,if_pos hz,readGradient_oracle]
  exact (score_consider_le_norm q n _ _).trans_eq (congrArg (fun x => ‖gradient f x‖) ha)

theorem output_gradient_le_candidate (f : Point d → ℝ) (hq : 0<q) (N k : ℕ) (hk : (k+1)*q≤N)
    (seed : PUnit) :
    ‖gradient f ((policy d hD η m q N).output
      ((policy d hD η m q N).run (ordinaryOracle f) (richOracle f) (1+4*N) seed))‖≤
        ‖gradient f ((actualIterates hD η m q f).candidate q k)‖ := by
  rw [machine_output,← score_states_correct]
  exact (score_states_antitone hD η m q (ordinaryOracle f) (richOracle f) hk).trans
    (score_completed_block_le hD η m q f hq k)

end GradientHessian.NalenPolicy
