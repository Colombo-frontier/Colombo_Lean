import LowRank.BlockOrthogonal
import LowRank.BlockQueryRecovery

/-! Full factorization data, including cumulative row and column bases. One
revelation updates these bases and preserves the represented original matrix. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

abbrev FactorData (d t q r s : ℕ) :=
  (Matrix (Fin q) (Fin q) ℝ × Matrix (Fin r) (Fin q) ℝ) ×
    (Matrix (Fin d) (Fin q ⊕ Fin r) ℝ × Matrix (Fin t) (Fin q ⊕ Fin s) ℝ)

def representedMatrix {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) : Matrix (Fin d) (Fin t) ℝ :=
  st.2.1 * fromBlocks st.1.1 0 st.1.2 D * st.2.2ᵀ

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}

def updateFactorData (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (st : FactorData d t q (r + 1) (s + 1))
    (exposed : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : FactorData d t (q + 1) r s :=
  let C := rotateMatrixColumns b (rowGauge b u) st.1.2
  let L := extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u))
  let R := extendGauge (a := Fin q) (gaugeMatrix c (rowGauge c exposed.1))
  ((nextExposedA st.1.1 C ‖(basisCoordinates c).symm exposed.1‖, nextExposedC C exposed.2),
    (changedBasis st.2.1 L (moveFirstTail q r), changedBasis st.2.2 R (moveFirstTail q s)))

theorem full_block_rotation_update (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin (r + 1)) (Fin q) ℝ)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    let Y := rotateMatrixColumns b (rowGauge b u) D
    let C' := rotateMatrixColumns b (rowGauge b u) C
    let L := extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u))
    let R := extendGauge (a := Fin q) (gaugeMatrix c (rowGauge c (Y 0)))
    (L * fromBlocks A 0 C D * Rᵀ).submatrix (moveFirstTail q r) (moveFirstTail q s) =
      fromBlocks (nextExposedA A C' ‖(basisCoordinates c).symm (Y 0)‖) 0
        (nextExposedC C' (revealGaussianBlock c Y).1.2) (revealGaussianBlock c Y).2 := by
  dsimp only
  have heq : extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u)) * fromBlocks A 0 C D *
      (extendGauge (a := Fin q) (gaugeMatrix c
        (rowGauge c (rotateMatrixColumns b (rowGauge b u) D 0))))ᵀ =
      fromBlocks A 0 (rotateMatrixColumns b (rowGauge b u) C)
        (rotateMatrixRows c (rowGauge c (rotateMatrixColumns b (rowGauge b u) D 0))
          (rotateMatrixColumns b (rowGauge b u) D)) := by
    simp only [extendGauge, fromBlocks_transpose, fromBlocks_multiply,
      transpose_one, transpose_zero, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [← rotateMatrixColumns_eq_mul, ← rotateMatrixColumns_eq_mul, ← rotateMatrixRows_eq_mul]
  rw [heq]
  exact revealed_full_block_update c A _ _

theorem updateFactorData_preserves_matrix (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (st : FactorData d t q (r + 1) (s + 1))
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    let Y := rotateMatrixColumns b (rowGauge b u) D
    let out := revealGaussianBlock c Y
    representedMatrix (updateFactorData b c u st out.1) out.2 = representedMatrix st D := by
  let Y := rotateMatrixColumns b (rowGauge b u) D
  let L := extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u))
  let R := extendGauge (a := Fin q) (gaugeMatrix c (rowGauge c (Y 0)))
  have hL : Lᵀ * L = 1 := extendGauge_transpose_mul _ (gaugeMatrix_transpose_mul_self b _)
  have hR : Rᵀ * R = 1 := extendGauge_transpose_mul _ (gaugeMatrix_transpose_mul_self c _)
  have h := changedBasis_reconstruct st.2.1 st.2.2 (fromBlocks st.1.1 0 st.1.2 D)
    L R (moveFirstTail q r) (moveFirstTail q s) hL hR
  have hb := full_block_rotation_update b c u st.1.1 st.1.2 D
  change (L * fromBlocks st.1.1 0 st.1.2 D * Rᵀ).submatrix _ _ = _ at hb
  rw [hb] at h
  exact h

theorem updateFactorData_A_injective (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (st : FactorData d t q (r + 1) (s + 1))
    (exposed : (Fin (s + 1) → ℝ) × (Fin r → ℝ))
    (hA : Function.Injective (Matrix.mulVec st.1.1))
    (hρ : ‖(basisCoordinates c).symm exposed.1‖ ≠ 0) :
    Function.Injective (Matrix.mulVec (updateFactorData b c u st exposed).1.1) :=
  nextExposedA_injective _ _ hρ hA

end
end LowRank
