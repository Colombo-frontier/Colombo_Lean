import LowRank.GaussianModel

/-! Block diagonal matrices with a scalar leading coordinate and a finite
tail block, indexed directly by Fin (d+1) for recursive spectral choice. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def leadingBlock {d : ℕ} (a : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

theorem leadingBlock_transpose {d : ℕ} (a : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    (leadingBlock a A)ᵀ = leadingBlock a Aᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem leadingBlock_one (d : ℕ) : leadingBlock 1 (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [leadingBlock, Matrix.one_apply, eq_comm]

theorem leadingBlock_mul {d : ℕ} (a b : ℝ) (A B : Matrix (Fin d) (Fin d) ℝ) :
    leadingBlock a A * leadingBlock b B = leadingBlock (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, leadingBlock]

theorem leadingBlock_diagonal {d : ℕ} (a : ℝ) (lam : Fin d → ℝ) :
    leadingBlock a (diagonal lam) = diagonal (Fin.cons a lam) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [leadingBlock, Matrix.diagonal_apply, eq_comm]

theorem leadingBlock_orthogonal {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) (hU : Uᵀ * U = 1) :
    (leadingBlock 1 U)ᵀ * leadingBlock 1 U = 1 := by
  rw [leadingBlock_transpose, leadingBlock_mul, hU, one_mul, leadingBlock_one]

theorem measurable_leadingBlock (d : ℕ) : Measurable
    (fun z : ℝ × Matrix (Fin d) (Fin d) ℝ => leadingBlock z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
      simp only [leadingBlock, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

end
end LowRank
