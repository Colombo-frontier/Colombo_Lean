import Problem254
import Audit254
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.StarOrdered

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace Paper254

abbrev Coordinates (d : ℕ) := Fin d → ℝ
abbrev Precision (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def matrixQuadratic {d : ℕ} (A : Precision d) (x : Coordinates d) : ℝ := x ⬝ᵥ (A *ᵥ x)

theorem matrixQuadratic_nonneg {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (x : Coordinates d) : 0 ≤ matrixQuadratic A x := by
  simpa [matrixQuadratic] using hA.posSemidef.2 x

structure PrecisionGaussian (d : ℕ) where
  mean : Coordinates d
  precision : Precision d
  positive : precision.PosDef

def precisionCovariancePart {d : ℕ} (q : ℝ) (A : Precision d) : ℝ :=
  q*A.trace-d-Real.log (q^d*A.det)

def PrecisionGaussian.potential {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (u : Coordinates d) : ℝ :=
  (precisionCovariancePart q P.precision+matrixQuadratic P.precision (u-P.mean))/2

theorem precisionCovariancePart_spectral {d : ℕ} (q : ℝ) (hq : 0 < q)
    {A : Precision d} (hA : A.PosDef) :
    precisionCovariancePart q A =
      ∑ j, (q*hA.isHermitian.eigenvalues j-1-Real.log (q*hA.isHermitian.eigenvalues j)) := by
  have hprod : q^d*A.det = ∏ j, q*hA.isHermitian.eigenvalues j := by
    rw [Finset.prod_mul_distrib, hA.isHermitian.det_eq_prod_eigenvalues]
    simp
  rw [precisionCovariancePart, hA.isHermitian.trace_eq_sum_eigenvalues, hprod,
    Real.log_prod Finset.univ _ (fun j _ => ne_of_gt (mul_pos hq (hA.eigenvalues_pos j)))]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq]

theorem precisionCovariancePart_nonneg {d : ℕ} (q : ℝ) (hq : 0 < q)
    {A : Precision d} (hA : A.PosDef) : 0 ≤ precisionCovariancePart q A := by
  rw [precisionCovariancePart_spectral q hq hA]
  apply Finset.sum_nonneg
  intro j _
  have hh := Real.log_le_sub_one_of_pos (mul_pos hq (hA.eigenvalues_pos j))
  linarith

theorem PrecisionGaussian.potential_nonneg {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (hq : 0 < q) (u : Coordinates d) : 0 ≤ P.potential q u := by
  exact div_nonneg (add_nonneg (precisionCovariancePart_nonneg q hq P.positive)
    (matrixQuadratic_nonneg P.positive _)) (by norm_num)

def rankOnePrecision {d : ℕ} (A : Precision d) (θ : ℝ) (g : Coordinates d) : Precision d :=
  A+θ • Matrix.vecMulVec g g

theorem rankOnePrecision_posDef {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (θ : ℝ) (hθ : 0 ≤ θ) (g : Coordinates d) : (rankOnePrecision A θ g).PosDef := by
  have hg : (Matrix.vecMulVec g g).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star g
  exact hA.add_posSemidef (hg.smul hθ)

theorem rankOnePrecision_trace {d : ℕ} (A : Precision d) (θ : ℝ) (g : Coordinates d) :
    (rankOnePrecision A θ g).trace = A.trace+θ*(g ⬝ᵥ g) := by
  simp [rankOnePrecision, Matrix.trace_add, Matrix.trace_smul]

theorem rankOnePrecision_quadratic {d : ℕ} (A : Precision d)
    (θ : ℝ) (g x : Coordinates d) :
    matrixQuadratic (rankOnePrecision A θ g) x = matrixQuadratic A x+θ*(g ⬝ᵥ x)^2 := by
  simp only [matrixQuadratic, rankOnePrecision, Matrix.add_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, Matrix.vecMulVec_mulVec, smul_eq_mul]
  rw [dotProduct_comm x g]
  simp only [op_smul_eq_mul]
  ring

def PrecisionGaussian.tilt {d : ℕ} (P : PrecisionGaussian d)
    (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (g w : Coordinates d) : PrecisionGaussian d :=
  let A := rankOnePrecision P.precision (lam*γ) g
  let b := P.precision *ᵥ P.mean-lam • g+(lam*γ*(g ⬝ᵥ w)) • g
  ⟨A⁻¹ *ᵥ b, A, rankOnePrecision_posDef P.positive (lam*γ) (mul_nonneg hlam hγ) g⟩

end Paper254
#print axioms Paper254.PrecisionGaussian.potential_nonneg
#print axioms Paper254.rankOnePrecision_posDef
#print axioms Paper254.rankOnePrecision_quadratic
