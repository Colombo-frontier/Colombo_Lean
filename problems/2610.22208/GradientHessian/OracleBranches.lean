import GradientHessian.OracleComposition

/-! Exact independent-branch evaluation after one shared preprocessing state.
The sequential implementation keeps every branch's original input and ignores
other branch outputs when selecting its queries. -/

namespace GradientHessian.OracleComposition.Procedure
open MeasureTheory Matrix LowRank
noncomputable section
variable {d p q : ℕ} {S T O : Type*}
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]

def pure (f : MeasurableStateMap S O) : Procedure d 0 S O where
  policy := PUnit.unit
  decode := f

theorem run_pure (f : MeasurableStateMap S O) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    (pure (d := d) f).run A s = f.1 s := rfl

def withSeed (P : Procedure d q S O) : Procedure d q S (S × O) where
  policy := P.policy
  decode := ⟨fun h => (oracleHistorySeed d q h, P.decode.1 h),
    (measurable_oracleHistorySeed d q S).prodMk P.decode.2⟩

theorem run_withSeed (P : Procedure d q S O) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    P.withSeed.run A s = (s, P.run A s) := by
  change (oracleHistorySeed d q (runAmbientOracle d q P.policy A s), P.run A s) = _
  rw [oracleHistorySeed_runAmbientOracle]

def parallelPair (P : Procedure d p S T) (Q : Procedure d q S O) :
    Procedure d (p + q) S (T × O) :=
  P.withSeed.bind ((Q.comap ⟨Prod.fst, measurable_fst⟩).withSeed.mapOutput
    ⟨fun t : (S × T) × O => (t.1.2, t.2), measurable_fst.snd.prodMk measurable_snd⟩)

theorem run_parallelPair (P : Procedure d p S T) (Q : Procedure d q S O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    (P.parallelPair Q).run A s = (P.run A s, Q.run A s) := by
  simp only [parallelPair, run_bind, run_withSeed, run_mapOutput, run_comap]

def consOutput (r : ℕ) : MeasurableStateMap (O × (Fin r → O)) (Fin (r + 1) → O) :=
  ⟨fun t => Fin.cons t.1 t.2, by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact measurable_fst
    | succ i => exact (measurable_pi_apply i).comp measurable_snd⟩

def parallel : (r : ℕ) → (Fin r → Procedure d q S O) → Procedure d (r * q) S (Fin r → O)
  | 0, _ => (pure (d := d) (S := S) (O := Fin 0 → O)
      ⟨fun _ i => Fin.elim0 i, measurable_const⟩).castBudget (Nat.zero_mul q).symm
  | r + 1, P =>
      (((P 0).parallelPair (parallel r (fun i => P i.succ))).mapOutput (consOutput r)).castBudget
        (by rw [Nat.succ_mul]; omega)

theorem run_parallel (r : ℕ) (P : Fin r → Procedure d q S O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) (i : Fin r) :
    (parallel r P).run A s i = (P i).run A s := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      simp only [parallel, run_castBudget, run_mapOutput, run_parallelPair]
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih (fun j => P j.succ) i

/-- A preprocessor runs exactly once. Each postprocessor then sees the same
saved state; no query choice in one branch can depend on another's replies. -/
def fork (pre : Procedure d p S T) (r : ℕ) (post : Fin r → Procedure d q T O) :
    Procedure d (p + r * q) S (Fin r → O) := pre.bind (parallel r post)

theorem run_fork (pre : Procedure d p S T) (r : ℕ) (post : Fin r → Procedure d q T O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) (i : Fin r) :
    (pre.fork r post).run A s i = (post i).run A (pre.run A s) := by
  rw [fork, run_bind, run_parallel]

theorem fork_calls (pre : Procedure d p S T) (r : ℕ) (post : Fin r → Procedure d q T O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : S) :
    ((pre.fork r post).toProgram s).calls oracle = p + r * q :=
  calls_toProgram _ oracle s

end
end GradientHessian.OracleComposition.Procedure
