import GradientHessian.OracleComposition
import GradientHessian.MatrixSandwichOracle

/-! A measurable, exact one-product simulation of the literal source matrix.
The memory map reconstructs each original reply from one simulated reply. -/

namespace GradientHessian.OracleSimulation
open Matrix MeasureTheory LowRank OracleComposition
noncomputable section

variable {d : ℕ} {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

def nextMemory (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ)
    (query : MeasurableStateMap S (Fin d → ℝ)) (mem : MeasurableStateMap T S) :
    MeasurableStateMap (T × (Fin d → ℝ)) (S × (Fin d → ℝ)) :=
  ⟨fun t => (mem.1 t.1, query.1 (mem.1 t.1) + scale • (D *ᵥ t.2)), by
    apply (mem.2.comp measurable_fst).prodMk
    apply Measurable.add ((query.2.comp mem.2).comp measurable_fst)
    apply measurable_pi_lambda
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    fun_prop⟩

def policy (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ) :
    (n : ℕ) → {S T : Type*} → [MeasurableSpace S] → [MeasurableSpace T] →
      AmbientOraclePolicy d n S → MeasurableStateMap T S → AmbientOraclePolicy d n T
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n + 1, _, _, _, _, p, mem =>
      (⟨fun t => D *ᵥ p.1.1 (mem.1 t), by
        have hquery : Measurable (fun t => p.1.1 (mem.1 t)) := p.1.2.comp mem.2
        apply measurable_pi_lambda
        intro i
        simp only [Matrix.mulVec, dotProduct]
        fun_prop⟩, policy scale D n p.2 (nextMemory scale D p.1 mem))

def decodeHistory (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ) :
    (n : ℕ) → {S T : Type*} → [MeasurableSpace S] → [MeasurableSpace T] →
      AmbientOraclePolicy d n S → MeasurableStateMap T S →
        OracleHistory d n T → OracleHistory d n S
  | 0, _, _, _, _, _, mem, h => mem.1 h
  | n + 1, _, _, _, _, p, mem, h =>
      decodeHistory scale D n p.2 (nextMemory scale D p.1 mem) h

theorem decodeHistory_measurable (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (p : AmbientOraclePolicy d n S) (mem : MeasurableStateMap T S) :
    Measurable (decodeHistory scale D n p mem) := by
  induction n generalizing S T with
  | zero => exact mem.2
  | succ n ih => exact ih p.2 (nextMemory scale D p.1 mem)

theorem run_policy (scale : ℝ) (D W : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (p : AmbientOraclePolicy d n S) (mem : MeasurableStateMap T S) (t : T) :
    decodeHistory scale D n p mem (runAmbientOracle d n (policy scale D n p mem) W t) =
      runAmbientOracle d n p (MatrixSandwichOracle.transformedMatrix scale D W) (mem.1 t) := by
  induction n generalizing S T with
  | zero => rfl
  | succ n ih =>
      change decodeHistory scale D n p.2 (nextMemory scale D p.1 mem)
        (runAmbientOracle d n (policy scale D n p.2 (nextMemory scale D p.1 mem)) W
          (t, W *ᵥ (D *ᵥ p.1.1 (mem.1 t)))) = _
      rw [ih]
      simp only [runAmbientOracle, nextMemory, MatrixSandwichOracle.transformedMatrix_mulVec]

def procedure {n : ℕ} {O : Type*} [MeasurableSpace O]
    (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ) (P : Procedure d n S O) : Procedure d n S O where
  policy := policy scale D n P.policy ⟨id, measurable_id⟩
  decode := ⟨fun h => P.decode.1 (decodeHistory scale D n P.policy ⟨id, measurable_id⟩ h),
    P.decode.2.comp (decodeHistory_measurable scale D n P.policy ⟨id, measurable_id⟩)⟩

theorem run_procedure {n : ℕ} {O : Type*} [MeasurableSpace O]
    (scale : ℝ) (D W : Matrix (Fin d) (Fin d) ℝ) (P : Procedure d n S O) (s : S) :
    (procedure scale D P).run W s =
      P.run (MatrixSandwichOracle.transformedMatrix scale D W) s := by
  exact congrArg P.decode.1 (run_policy scale D W n P.policy ⟨id, measurable_id⟩ s)

theorem procedure_calls {n : ℕ} {O : Type*} [MeasurableSpace O]
    (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ) (P : Procedure d n S O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : S) :
    ((procedure scale D P).toProgram s).calls oracle = n :=
  Procedure.calls_toProgram _ oracle s

end
end GradientHessian.OracleSimulation
