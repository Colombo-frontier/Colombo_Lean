import LowRank.ProjectorRank
import LowRank.GaussianModel
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! A total measurable projector onto a single vector, including the zero
vector. This is the building block for a measurable column-space projector. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem outer_mulVec {d t : ℕ} (u : Fin d → ℝ) (v x : Fin t → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mul_outer {a d t : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (u : Fin d → ℝ) (v : Fin t → ℝ) :
    A * vecMulVec u v = vecMulVec (A *ᵥ u) v := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

def rankOneProjector {d : ℕ} (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (v ⬝ᵥ v)⁻¹ • vecMulVec v v

theorem rankOneProjector_zero (d : ℕ) : rankOneProjector (0 : Fin d → ℝ) = 0 := by
  simp [rankOneProjector, dotProduct]

theorem rankOneProjector_symmetric {d : ℕ} (v : Fin d → ℝ) :
    (rankOneProjector v)ᵀ = rankOneProjector v := by
  ext i j
  simp only [rankOneProjector, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, vecMulVec_apply]
  ring

theorem rankOneProjector_fixes {d : ℕ} (v : Fin d → ℝ) :
    rankOneProjector v *ᵥ v = v := by
  by_cases hv : v = 0
  · simp [hv, rankOneProjector_zero]
  · have hdot : v ⬝ᵥ v ≠ 0 := fun h => hv (_root_.dotProduct_self_eq_zero.mp h)
    rw [rankOneProjector, Matrix.smul_mulVec_assoc, outer_mulVec, smul_smul,
      inv_mul_cancel₀ hdot, one_smul]

theorem rankOneProjector_isProjector {d : ℕ} (v : Fin d → ℝ) :
    IsOrthogonalProjector (rankOneProjector v) := by
  refine ⟨rankOneProjector_symmetric v, ?_⟩
  calc
    _ = (v ⬝ᵥ v)⁻¹ • (rankOneProjector v * vecMulVec v v) := by
      conv_lhs => rhs; unfold rankOneProjector
      rw [Matrix.mul_smul]
    _ = rankOneProjector v := by rw [mul_outer, rankOneProjector_fixes]; rfl

theorem rankOneProjector_trace {d : ℕ} (v : Fin d → ℝ) :
    (rankOneProjector v).trace = if v = 0 then 0 else 1 := by
  by_cases hv : v = 0
  · simp [hv, rankOneProjector_zero]
  · have hdot : v ⬝ᵥ v ≠ 0 := fun h => hv (_root_.dotProduct_self_eq_zero.mp h)
    rw [if_neg hv, rankOneProjector, Matrix.trace_smul]
    change (v ⬝ᵥ v)⁻¹ * (v ⬝ᵥ v) = 1
    exact inv_mul_cancel₀ hdot

theorem rankOneProjector_trace_le_one {d : ℕ} (v : Fin d → ℝ) :
    (rankOneProjector v).trace ≤ 1 := by
  rw [rankOneProjector_trace]
  split_ifs <;> norm_num

theorem mul_rankOneProjector_eq_zero {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (v : Fin d → ℝ) (hv : A *ᵥ v = 0) : A * rankOneProjector v = 0 := by
  rw [rankOneProjector, Matrix.mul_smul, mul_outer, hv]
  ext i j
  simp [Matrix.smul_apply, vecMulVec_apply]

theorem measurable_rankOneProjector (d : ℕ) :
    Measurable (rankOneProjector : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [rankOneProjector, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, dotProduct]
  exact ((Finset.measurable_sum Finset.univ (fun l _ =>
    (measurable_pi_apply l).mul (measurable_pi_apply l))).inv).mul
      ((measurable_pi_apply i).mul (measurable_pi_apply j))

end
end LowRank
