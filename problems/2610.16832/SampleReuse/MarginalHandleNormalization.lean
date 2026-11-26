import SampleReuse.MarginalGradientTable
import SampleReuse.PersistentHandleNormalization

/-! Reordering derivative requests exposes their opaque handle to the
generic finite-horizon normalization. Both gradient-call count and output
are preserved on the actual infinite immutable-sample execution. -/

open SecondOrder
open scoped Classical BigOperators
namespace SampleReuse
noncomputable section
variable {Ξ H S : Type} {d : ℕ} {R : ℝ}

def marginalAsPersistent (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S) :
    OracleAlgorithm ((Bool × Point d) × H) (PersistentReply d) (Point d) S where
  initial := P.initial
  query n s := let q := P.query n s; ((q.1,q.2.2),q.2.1)
  update := P.update
  output := P.output

def marginalFromPersistent (P : OracleAlgorithm ((Bool × Point d) × H) (PersistentReply d) (Point d) S) :
    OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S where
  initial := P.initial
  query n s := let q := P.query n s; (q.1.1,q.2,q.1.2)
  update := P.update
  output := P.output

def marginalLazyReply (ε : ℝ) (v : Point d) (q : Bool × Point d) (z : SignedCoefficient R) :
    PersistentReply d := marginalDecodedReply ε v (q.1,(),q.2) z.1

def normalizeMarginalOracle (N : ℕ)
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S) :=
  marginalFromPersistent (normalizePersistentAlgorithm N (marginalAsPersistent P))

theorem marginalPersistentRun_as_persistent
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (table : H → SignedCoefficient R) : ∀ n,
    marginalPersistentRun P.toQueryPolicy ε v table n =
      persistentQueryRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) table n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [marginalPersistentRun,persistentQueryRun,ih]
    rfl

theorem marginalFromPersistent_run
    (P : OracleAlgorithm ((Bool × Point d) × H) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (table : H → SignedCoefficient R) : ∀ n,
    marginalPersistentRun (marginalFromPersistent P).toQueryPolicy ε v table n =
      persistentQueryRun P.toQueryPolicy (marginalLazyReply ε v) table n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [marginalPersistentRun,persistentQueryRun,ih]
    rfl

theorem normalizeMarginalOracle_run (N : ℕ)
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (tape : ℕ → SignedCoefficient R) (n : ℕ) (hn : n ≤ N) :
    marginalPersistentRun (normalizeMarginalOracle N P).toQueryPolicy ε v (fun i => tape i.val) n =
      lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape n := by
  rw [normalizeMarginalOracle,marginalFromPersistent_run]
  exact normalizePersistentPolicy_run N (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v)
    (fun i => tape i.val) tape (fun _ => rfl) n hn

def marginalLazyObservation
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (N : ℕ) (w : Ξ × (ℕ → SignedCoefficient R)) : ℕ × Point d :=
  (∑ k ∈ Finset.range N, if ((P w.1).query k
      (lazyPersistentRun (marginalAsPersistent (P w.1)).toQueryPolicy (marginalLazyReply ε v) w.2 k).1).1
      then 1 else 0,
    (P w.1).output N
      (lazyPersistentRun (marginalAsPersistent (P w.1)).toQueryPolicy (marginalLazyReply ε v) w.2 N).1)

theorem normalized_marginal_observation
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (N : ℕ) (w : Ξ × (ℕ → SignedCoefficient R)) :
    marginalTableObservation (fun ξ => normalizeMarginalOracle N (P ξ)) ε v N
      (w.1,fun i => w.2 i.val) = marginalLazyObservation P ε v N w := by
  apply Prod.ext
  · dsimp only [marginalTableObservation,marginalLazyObservation]
    apply Finset.sum_congr rfl
    intro k hk
    rw [normalizeMarginalOracle_run N (P w.1) ε v w.2 k (by simpa using (Finset.mem_range.mp hk).le)]
    rfl
  · dsimp only [marginalTableObservation,marginalLazyObservation]
    rw [normalizeMarginalOracle_run N (P w.1) ε v w.2 N le_rfl]
    rfl

end
end SampleReuse
