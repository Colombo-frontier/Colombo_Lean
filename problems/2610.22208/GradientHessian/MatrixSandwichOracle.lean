import LowRank.PolicyOutputMap
import Mathlib.Tactic

/-! The literal source matrix A = I + scale D W D: every A product is exactly
one W product, including on counterfactual inputs outside the analytic event. -/

namespace GradientHessian.MatrixSandwichOracle

open Matrix MeasureTheory LowRank
noncomputable section

def transformedMatrix {d : ℕ} (scale : ℝ)
    (D W : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  1 + scale • (D * W * D)

theorem transformedMatrix_symmetric {d : ℕ} (scale : ℝ)
    (D W : Matrix (Fin d) (Fin d) ℝ) (hD : Dᵀ = D) (hW : Wᵀ = W) :
    (transformedMatrix scale D W)ᵀ = transformedMatrix scale D W := by
  simp [transformedMatrix, transpose_mul, hD, hW, Matrix.mul_assoc]

theorem transformedMatrix_mulVec {d : ℕ} (scale : ℝ)
    (D W : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) :
    transformedMatrix scale D W *ᵥ z = z + scale • (D *ᵥ (W *ᵥ (D *ᵥ z))) := by
  simp [transformedMatrix, Matrix.add_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

def encode {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ)
    (q : Bool × (Fin d → ℝ)) : Fin d → ℝ := D *ᵥ q.2

def decode {d : ℕ} (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ)
    (q : Bool × (Fin d → ℝ)) (reply : Fin d → ℝ) : Fin d → ℝ :=
  q.2 + scale • (D *ᵥ reply)

theorem encode_measurable {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (encode D) := by
  apply measurable_pi_lambda
  intro i
  simp only [encode, Matrix.mulVec, dotProduct]
  fun_prop

theorem decode_measurable {d : ℕ} (scale : ℝ) (D : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (Function.uncurry (decode scale D)) := by
  apply measurable_pi_lambda
  intro i
  simp only [Function.uncurry, decode, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  fun_prop

theorem decode_reply {d : ℕ} (scale : ℝ) (D W : Matrix (Fin d) (Fin d) ℝ)
    (hD : Dᵀ = D) (hW : Wᵀ = W) (q : Bool × (Fin d → ℝ)) :
    decode scale D q (W *ᵥ encode D q) = twoSidedOracle (transformedMatrix scale D W) q := by
  rw [symmetric_twoSidedOracle (transformedMatrix_symmetric scale D W hD hW),
    transformedMatrix_mulVec]
  rfl

/-- Both the exact output and the exact call count are preserved. No spectral
or probability assumption enters this simulation. -/
theorem simulate_exact {d : ℕ} {O : Type*} (scale : ℝ)
    (D W : Matrix (Fin d) (Fin d) ℝ) (hD : Dᵀ = D) (hW : Wᵀ = W)
    (program : OracleProgram (Bool × (Fin d → ℝ)) (Fin d → ℝ) O) :
    (program.simulate (encode D) (decode scale D)).eval (fun z => W *ᵥ z) =
        program.eval (twoSidedOracle (transformedMatrix scale D W)) ∧
      (program.simulate (encode D) (decode scale D)).calls (fun z => W *ᵥ z) =
        program.calls (twoSidedOracle (transformedMatrix scale D W)) :=
  ⟨OracleProgram.eval_simulate _ _ _ _ (decode_reply scale D W hD hW) program,
   OracleProgram.calls_simulate _ _ _ _ (decode_reply scale D W hD hW) program⟩

theorem simulate_budget {d n : ℕ} {O : Type*} (scale : ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ)
    (program : OracleProgram (Bool × (Fin d → ℝ)) (Fin d → ℝ) O)
    (hbudget : program.HasBudget n) :
    (program.simulate (encode D) (decode scale D)).HasBudget n :=
  OracleProgram.budget_simulate _ _ hbudget

end
end GradientHessian.MatrixSandwichOracle
