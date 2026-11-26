import GradientHessian.NalenPolicy
import GradientHessian.NalenDirection

/-! Exact execution of the finite NALEN schedule as literal four-phase
cycles. The recurrence is derived from the compiled Machine.Policy. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen

variable {d : ℕ} {D : ℝ} (hD : 0≤D) (η : ℝ) (m q : ℕ)
  (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d)

def refresh (m : ℕ) (rich : Point d → RichReply d) (n : ℕ) (s : Data (Point d)) : Data (Point d) :=
  if n%m=0 then snapshot s (readHessian (rich (Nalen.midpoint (position s) (delta s)))) else s

def prediction (s : Data (Point d)) : Data (Point d) :=
  predict hD η s (readGradient (ordinary (Nalen.midpoint (position s) (delta s))))

def correction (n : ℕ) (s : Data (Point d)) : Data (Point d) :=
  correct hD η n s (readGradient (ordinary (Nalen.midpoint (position s) (delta s))))

def candidateCheck (q : ℕ) (ordinary : Point d → OrdinaryReply d) (n : ℕ) (s : Data (Point d)) : Data (Point d) :=
  if (n+1)%q=0 then consider q n s (readGradient (ordinary (average q n s))) else s

def cycle (n : ℕ) (s : Data (Point d)) : Data (Point d) :=
  candidateCheck q ordinary n (correction hD η ordinary n (prediction hD η ordinary (refresh m rich n s)))

def states : ℕ → Data (Point d)
  | 0 => initial D (readGradient (ordinary 0))
  | n+1 => cycle hD η m q ordinary rich n (states n)

theorem advance_snapshot (N n : ℕ) (s : Data (Point d)) :
    (program d hD η m q N).advance ordinary rich (1+4*n) s=refresh m rich n s := by
  have h0 : 1+4*n≠0 := by omega
  have hp := phase_clock n 0 (by omega)
  have hi := iteration_clock n 0 (by omega)
  simp only [Nat.add_zero] at hp hi
  by_cases h : n%m=0 <;>
    simp [ClockedOracle.Program.advance,program,kind_snapshot,h,queryPoint,h0,hp,hi,richUpdate,refresh]

theorem advance_prediction (N n : ℕ) (s : Data (Point d)) :
    (program d hD η m q N).advance ordinary rich (1+4*n+1) s=prediction hD η ordinary s := by
  have h0 : 1+4*n+1≠0 := by omega
  simp [ClockedOracle.Program.advance,program,kind_predict,ordinaryUpdate,queryPoint,h0,
    phase_clock n 1 (by omega),prediction]

theorem advance_correction (N n : ℕ) (s : Data (Point d)) :
    (program d hD η m q N).advance ordinary rich (1+4*n+2) s=correction hD η ordinary n s := by
  have h0 : 1+4*n+2≠0 := by omega
  simp [ClockedOracle.Program.advance,program,kind_correct,ordinaryUpdate,queryPoint,h0,
    phase_clock n 2 (by omega),iteration_clock n 2 (by omega),correction]

theorem advance_candidate (N n : ℕ) (s : Data (Point d)) :
    (program d hD η m q N).advance ordinary rich (1+4*n+3) s=candidateCheck q ordinary n s := by
  have h0 : 1+4*n+3≠0 := by omega
  by_cases h : (n+1)%q=0 <;>
    simp [ClockedOracle.Program.advance,program,kind_candidate,h,ordinaryUpdate,queryPoint,h0,
      phase_clock n 3 (by omega),iteration_clock n 3 (by omega),candidateCheck]

theorem evaluate_cycle (N n : ℕ) (seed : PUnit) :
    (program d hD η m q N).evaluate ordinary rich (1+4*(n+1)) seed=
      cycle hD η m q ordinary rich n ((program d hD η m q N).evaluate ordinary rich (1+4*n) seed) := by
  have he : 1+4*(n+1)=(1+4*n)+1+1+1+1 := by omega
  have h2 : 1+4*n+1+1=1+4*n+2 := by omega
  have h3 : 1+4*n+1+1+1=1+4*n+3 := by omega
  rw [he]
  simp only [ClockedOracle.Program.evaluate]
  rw [h2,h3,advance_candidate,advance_correction,advance_prediction,advance_snapshot]
  rfl

theorem evaluate_states (N n : ℕ) (seed : PUnit) :
    (program d hD η m q N).evaluate ordinary rich (1+4*n) seed=states hD η m q ordinary rich n := by
  induction n with
  | zero => simp [ClockedOracle.Program.evaluate,ClockedOracle.Program.advance,program,kind,ordinaryUpdate,queryPoint,states]
  | succ n ih => rw [evaluate_cycle,ih]; rfl

theorem machine_states (N n : ℕ) (hn : n≤N) (seed : PUnit) :
    (policy d hD η m q N).run ordinary rich (1+4*n) seed=(1+4*n,states hD η m q ordinary rich n) := by
  rw [policy,(program d hD η m q N).run_prefix ordinary rich _ (by change 1+4*n≤1+4*N; omega) seed,
    evaluate_states]

theorem machine_output (N : ℕ) (seed : PUnit) :
    (policy d hD η m q N).output ((policy d hD η m q N).run ordinary rich (1+4*N) seed)=
      best (states hD η m q ordinary rich N) := by
  rw [machine_states hD η m q ordinary rich N N le_rfl seed]
  rfl

@[simp] theorem position_refresh (m n : ℕ) (rich : Point d → RichReply d) (s : Data (Point d)) : position (refresh m rich n s)=position s := by
  unfold refresh
  split_ifs <;> simp
@[simp] theorem delta_refresh (m n : ℕ) (rich : Point d → RichReply d) (s : Data (Point d)) : delta (refresh m rich n s)=delta s := by
  unfold refresh
  split_ifs <;> simp
@[simp] theorem prox_refresh (m n : ℕ) (rich : Point d → RichReply d) (s : Data (Point d)) : prox (refresh m rich n s)=prox s := by
  unfold refresh
  split_ifs <;> simp
@[simp] theorem queries_refresh (m n : ℕ) (rich : Point d → RichReply d) (s : Data (Point d)) : queries (refresh m rich n s)=queries s := by
  unfold refresh
  split_ifs <;> simp

@[simp] theorem position_candidateCheck (q n : ℕ) (ordinary : Point d → OrdinaryReply d) (s : Data (Point d)) : position (candidateCheck q ordinary n s)=position s := by
  unfold candidateCheck
  split_ifs <;> simp
@[simp] theorem delta_candidateCheck (q n : ℕ) (ordinary : Point d → OrdinaryReply d) (s : Data (Point d)) : delta (candidateCheck q ordinary n s)=delta s := by
  unfold candidateCheck
  split_ifs <;> simp
@[simp] theorem prox_candidateCheck (q n : ℕ) (ordinary : Point d → OrdinaryReply d) (s : Data (Point d)) : prox (candidateCheck q ordinary n s)=prox s := by
  unfold candidateCheck
  split_ifs <;> simp
@[simp] theorem queries_candidateCheck (q n : ℕ) (ordinary : Point d → OrdinaryReply d) (s : Data (Point d)) : queries (candidateCheck q ordinary n s)=queries s := by
  unfold candidateCheck
  split_ifs <;> simp
@[simp] theorem matrix_candidateCheck (q n : ℕ) (ordinary : Point d → OrdinaryReply d) (s : Data (Point d)) : matrix (candidateCheck q ordinary n s)=matrix s := by
  unfold candidateCheck
  split_ifs <;> simp

def iterates : Nalen.Iterates (Point d) where
  x := fun n => position (states hD η m q ordinary rich n)
  δ := fun n => delta (states hD η m q ordinary rich n)
  v := fun n => prox (states hD η m q ordinary rich n)
  B := fun n => matrix (refresh m rich n (states hD η m q ordinary rich n))

theorem cycle_delta (n : ℕ) (s : Data (Point d)) :
    delta (cycle hD η m q ordinary rich n s)=quadraticBorelStep hD
      (readGradient (ordinary (Nalen.midpoint (position s) (delta s))),
        matrix (refresh m rich n s),delta s,prox s,η) := by
  simp [cycle,correction,prediction,correct,predict]

theorem cycle_position (n : ℕ) (s : Data (Point d)) :
    position (cycle hD η m q ordinary rich n s)=position s+delta (cycle hD η m q ordinary rich n s) := by
  simp [cycle,correction,prediction,correct,predict]

theorem cycle_prox (n : ℕ) (s : Data (Point d)) :
    prox (cycle hD η m q ordinary rich n s)=quadraticBorelStep hD
      (readGradient (ordinary (Nalen.midpoint (position s) (delta (cycle hD η m q ordinary rich n s)))),0,0,prox s,η) := by
  simp [cycle,correction,prediction,correct,predict]

theorem cycle_matrix (n : ℕ) (s : Data (Point d)) :
    matrix (cycle hD η m q ordinary rich n s)=matrix (refresh m rich n s) := by
  simp [cycle,correction,prediction,correct,predict]

theorem cycle_queries (n : ℕ) (s : Data (Point d)) :
    queries (cycle hD η m q ordinary rich n s)=
      Function.update (queries s) n (Nalen.midpoint (position s) (delta (cycle hD η m q ordinary rich n s))) := by
  simp [cycle,correction,prediction,correct,predict]

end GradientHessian.NalenPolicy
