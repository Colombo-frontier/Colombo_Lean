import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Exact matrix-vector simulations in `matvec.tex`

The matrices below are actual finite real matrices. The identities hold for
arbitrary real query vectors, not merely feasible game strategies. A product
with the symmetric dilation uses one two-sided query to the original matrix;
each game oracle identity uses two products with the source matrix.
-/

namespace Matvec

noncomputable section

open Matrix
open scoped Matrix

variable {d n m : Type*} [Fintype d] [Fintype n] [Fintype m]

/-- Symmetric dilation used in the proof of Theorem `thm:solve-lb`. -/
def dilation (G : Matrix d d ℝ) : Matrix (d ⊕ d) (d ⊕ d) ℝ :=
  Matrix.fromBlocks 0 G G.transpose 0

theorem dilation_mulVec (G : Matrix d d ℝ) (u v : d → ℝ) :
    dilation G *ᵥ Sum.elim u v = Sum.elim (G *ᵥ v) (G.transpose *ᵥ u) := by
  simp [dilation, Matrix.fromBlocks_mulVec]

omit [Fintype d] in
theorem dilation_transpose (G : Matrix d d ℝ) :
    (dilation G).transpose = dilation G := by
  simp [dilation, Matrix.fromBlocks_transpose]

/-- The homogeneous matrix `C` in equations (l21-C-row) and (l21-A).
The last coordinate is indexed by `Unit`; the positive and negative rows use
the two summands of `d ⊕ d`. The payoff matrix in the paper is `-C`. -/
def ballMatrix (H : Matrix d d ℝ) (b : d → ℝ) (α β : ℝ) :
    Matrix (d ⊕ d) (d ⊕ Unit) ℝ :=
  Matrix.fromBlocks (β • H) (fun i _ => α - β * b i)
    ((-β) • H) (fun i _ => α + β * b i)

theorem ballMatrix_mulVec (H : Matrix d d ℝ) (b z : d → ℝ) (α β s : ℝ) :
    ballMatrix H b α β *ᵥ Sum.elim z (fun _ => s) =
      Sum.elim (fun i => α * s + β * ((H *ᵥ z) i - s * b i))
        (fun i => α * s - β * ((H *ᵥ z) i - s * b i)) := by
  ext i
  cases i with
  | inl i =>
    simp [ballMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      mul_assoc, ← Finset.mul_sum]
    ring
  | inr i =>
    simp [ballMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      mul_assoc, ← Finset.mul_sum]
    ring

/-- The bounded simplex embedding, with arbitrary dictionaries `R` and `V`.
Its special dictionaries are `sqrt d [Q,-Q]` and `sqrt d [I,-I]`. -/
def simplexMatrix (H : Matrix d d ℝ) (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ) : Matrix m n ℝ :=
  Λ⁻¹ • (R.transpose * H * V - Matrix.vecMulVec (R.transpose *ᵥ b) (fun _ => 1))

omit [Fintype m] in
theorem simplexMatrix_mulVec (H : Matrix d d ℝ) (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ) (x : n → ℝ) :
    simplexMatrix H b R V Λ *ᵥ x =
      Λ⁻¹ • (R.transpose *ᵥ (H *ᵥ (V *ᵥ x) - (∑ j, x j) • b)) := by
  rw [simplexMatrix, Matrix.smul_mulVec_assoc, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul]
  congr 2
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, ← Finset.mul_sum,
    ← Finset.sum_mul, mul_comm]

theorem ballMatrix_transpose_mulVec (H : Matrix d d ℝ) (b : d → ℝ)
    (hH : H.transpose = H) (α β : ℝ) (yp ym : d → ℝ) :
    (ballMatrix H b α β).transpose *ᵥ Sum.elim yp ym =
      Sum.elim (β • (H *ᵥ (yp - ym)))
        (fun _ => α * ((∑ i, yp i) + ∑ i, ym i) - β * dotProduct b (yp - ym)) := by
  ext j
  cases j with
  | inl j =>
    simp only [ballMatrix, Matrix.fromBlocks_transpose, Matrix.transpose_smul,
      hH, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.mulVec_sub, Matrix.smul_mulVec_assoc, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  | inr j =>
    simp [ballMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      sub_mul, add_mul, mul_sub, mul_assoc]
    simp only [← Finset.mul_sum]
    ring

omit [Fintype n] in
theorem simplexMatrix_transpose_mulVec (H : Matrix d d ℝ) (b : d → ℝ)
    (hH : H.transpose = H) (R : Matrix d m ℝ) (V : Matrix d n ℝ)
    (Λ : ℝ) (y : m → ℝ) :
    (simplexMatrix H b R V Λ).transpose *ᵥ y =
      Λ⁻¹ • (V.transpose *ᵥ (H *ᵥ (R *ᵥ y)) -
        (fun _ => dotProduct b (R *ᵥ y))) := by
  rw [simplexMatrix, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH,
    Matrix.smul_mulVec_assoc, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 2
  ext j
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.transpose_apply,
    Pi.sub_apply, mul_one, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.of_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [Fintype m] in
/-- An exact solution represented by a mass-one dictionary vector is a zero
payoff witness. Nonnegativity is a separate simplex feasibility obligation. -/
theorem simplexMatrix_zero_witness (H : Matrix d d ℝ) (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ) (x : n → ℝ)
    (hx : ∑ j, x j = 1) (hsolve : H *ᵥ (V *ᵥ x) = b) :
    simplexMatrix H b R V Λ *ᵥ x = 0 := by
  rw [simplexMatrix_mulVec, hx, one_smul, hsolve, sub_self,
    Matrix.mulVec_zero, smul_zero]

end
end Matvec
