import LowRank.StoppingGramSimulation
import LowRank.PolicyOutputMap

/-! Measurable finite procedures with exact hard query budgets. Composition
retains actual oracle histories; no matrix-dependent data enter as free advice. -/

namespace GradientHessian.OracleComposition
open MeasureTheory Matrix LowRank
noncomputable section

def historyMap (d : ℕ) : (n : ℕ) → {S T : Type*} → (S → T) →
    OracleHistory d n S → OracleHistory d n T
  | 0, _, _, f, h => f h
  | n + 1, _, _, f, h => historyMap d n (fun t => (f t.1, t.2)) h

theorem measurable_historyMap (d n : ℕ) {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T] (f : S → T) (hf : Measurable f) :
    Measurable (historyMap d n f) := by
  induction n generalizing S T with
  | zero => exact hf
  | succ n ih => exact ih _ ((hf.comp measurable_fst).prodMk measurable_snd)

def extendSeed {d : ℕ} {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (f : MeasurableStateMap S T) : MeasurableStateMap (S × (Fin d → ℝ)) (T × (Fin d → ℝ)) :=
  ⟨fun t => (f.1 t.1, t.2), (f.2.comp measurable_fst).prodMk measurable_snd⟩

def pullbackPolicy (d : ℕ) : (n : ℕ) → {S T : Type*} → [MeasurableSpace S] → [MeasurableSpace T] →
    AmbientOraclePolicy d n T → MeasurableStateMap S T → AmbientOraclePolicy d n S
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n + 1, _, _, _, _, p, f =>
      (⟨fun s => p.1.1 (f.1 s), p.1.2.comp f.2⟩, pullbackPolicy d n p.2 (extendSeed f))

theorem run_pullbackPolicy (d n : ℕ) {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (p : AmbientOraclePolicy d n T) (f : MeasurableStateMap S T)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    historyMap d n f.1 (runAmbientOracle d n (pullbackPolicy d n p f) A s) =
      runAmbientOracle d n p A (f.1 s) := by
  induction n generalizing S T with
  | zero => rfl
  | succ n ih =>
      exact ih p.2 (extendSeed f) (s, A *ᵥ p.1.1 (f.1 s))

/-- The ordering `q+p` permits direct recursion on the prefix length. The
public procedure bind below casts this once to the usual `p+q`. -/
def regroupHistory (d q : ℕ) : (p : ℕ) → {S : Type*} →
    OracleHistory d (q + p) S → OracleHistory d q (OracleHistory d p S)
  | 0, _, h => h
  | p + 1, _, h => regroupHistory d q p h

theorem measurable_regroupHistory (d q p : ℕ) {S : Type*} [MeasurableSpace S] :
    Measurable (regroupHistory d q p (S := S)) := by
  induction p generalizing S with
  | zero => exact measurable_id
  | succ p ih => exact ih (S := S × (Fin d → ℝ))

def appendPolicy (d q : ℕ) : (p : ℕ) → {S : Type*} → [MeasurableSpace S] →
    AmbientOraclePolicy d p S → AmbientOraclePolicy d q (OracleHistory d p S) →
      AmbientOraclePolicy d (q + p) S
  | 0, _, _, _, tail => tail
  | p + 1, _, _, head, tail => (head.1, appendPolicy d q p head.2 tail)

theorem run_appendPolicy (d q p : ℕ) {S : Type*} [MeasurableSpace S]
    (head : AmbientOraclePolicy d p S) (tail : AmbientOraclePolicy d q (OracleHistory d p S))
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    regroupHistory d q p (runAmbientOracle d (q + p) (appendPolicy d q p head tail) A s) =
      runAmbientOracle d q tail A (runAmbientOracle d p head A s) := by
  induction p generalizing S with
  | zero => rfl
  | succ p ih => exact ih head.2 tail (s, A *ᵥ head.1.1 s)

structure Procedure (d q : ℕ) (S O : Type*) [MeasurableSpace S] [MeasurableSpace O] where
  policy : AmbientOraclePolicy d q S
  decode : MeasurableStateMap (OracleHistory d q S) O

namespace Procedure
variable {d p q : ℕ} {S T O : Type*}
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]

def run (P : Procedure d q S O) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : O :=
  P.decode.1 (runAmbientOracle d q P.policy A s)

theorem run_measurable (P : Procedure d q S O) :
    Measurable (fun t : Matrix (Fin d) (Fin d) ℝ × S => P.run t.1 t.2) :=
  P.decode.2.comp (measurable_runAmbientOracle d q P.policy)

def toProgram (P : Procedure d q S O) (s : S) : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O :=
  (P.policy.toProgram d q s).mapOutput P.decode.1

theorem eval_toProgram (P : Procedure d q S O) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    (P.toProgram s).eval (fun z => A *ᵥ z) = P.run A s := by
  rw [toProgram, OracleProgram.eval_mapOutput, AmbientOraclePolicy.eval_toProgram]
  rfl

theorem calls_toProgram (P : Procedure d q S O) (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : S) :
    (P.toProgram s).calls oracle = q := by
  rw [toProgram, OracleProgram.calls_mapOutput, AmbientOraclePolicy.calls_toProgram]

def comap (P : Procedure d q T O) (f : MeasurableStateMap S T) : Procedure d q S O where
  policy := pullbackPolicy d q P.policy f
  decode := ⟨fun h => P.decode.1 (historyMap d q f.1 h),
    P.decode.2.comp (measurable_historyMap d q f.1 f.2)⟩

theorem run_comap (P : Procedure d q T O) (f : MeasurableStateMap S T)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (P.comap f).run A s = P.run A (f.1 s) := by
  exact congrArg P.decode.1 (run_pullbackPolicy d q P.policy f A s)

def mapOutput (P : Procedure d q S T) (f : MeasurableStateMap T O) : Procedure d q S O where
  policy := P.policy
  decode := ⟨fun h => f.1 (P.decode.1 h), f.2.comp P.decode.2⟩

theorem run_mapOutput (P : Procedure d q S T) (f : MeasurableStateMap T O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (P.mapOutput f).run A s = f.1 (P.run A s) := rfl

def bindRev (P : Procedure d p S T) (Q : Procedure d q T O) : Procedure d (q + p) S O where
  policy := appendPolicy d q p P.policy (Q.comap P.decode).policy
  decode := ⟨fun h => (Q.comap P.decode).decode.1 (regroupHistory d q p h),
    (Q.comap P.decode).decode.2.comp (measurable_regroupHistory d q p)⟩

theorem run_bindRev (P : Procedure d p S T) (Q : Procedure d q T O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (P.bindRev Q).run A s = Q.run A (P.run A s) := by
  change (Q.comap P.decode).decode.1
    (regroupHistory d q p (runAmbientOracle d (q + p)
      (appendPolicy d q p P.policy (Q.comap P.decode).policy) A s)) = _
  rw [run_appendPolicy]
  exact run_comap Q P.decode A (runAmbientOracle d p P.policy A s)

def castBudget {q' : ℕ} (h : q = q') (P : Procedure d q S O) : Procedure d q' S O := h ▸ P

theorem run_castBudget {q' : ℕ} (h : q = q') (P : Procedure d q S O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (P.castBudget h).run A s = P.run A s := by
  subst q'
  rfl

def bind (P : Procedure d p S T) (Q : Procedure d q T O) : Procedure d (p + q) S O :=
  (P.bindRev Q).castBudget (Nat.add_comm q p)

theorem run_bind (P : Procedure d p S T) (Q : Procedure d q T O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (P.bind Q).run A s = Q.run A (P.run A s) := by
  rw [bind, run_castBudget, run_bindRev]

def ofBounded (P : BoundedTwoSidedPolicy d O q S) : Procedure d q S O where
  policy := padSymmetricPolicy d q P
  decode := ⟨readPaddedSymmetricOutput d q P, measurable_readPaddedSymmetricOutput d q P⟩

theorem run_ofBounded (P : BoundedTwoSidedPolicy d O q S)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : Aᵀ = A) (s : S) :
    (ofBounded P).run A s = runBoundedTwoSided d q P A s :=
  padSymmetricPolicy_simulates d q P A hA s

end Procedure
end
end GradientHessian.OracleComposition
