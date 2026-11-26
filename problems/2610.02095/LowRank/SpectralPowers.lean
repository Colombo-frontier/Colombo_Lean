import LowRank.MatrixInterlacing
import LowRank.FrobeniusCompression

/-! Spectral power sums and the finite Schatten expression for real rectangular
matrices, defined from the actual eigenvalues of XᵀX. Extra zero singular
values are included when there are more columns than rows. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem OrderedMatrixSpectrum.value_nonneg {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (hA : A.PosSemidef) (i : Fin d) : 0 ≤ sp.value i := by
  have h := hA.conjTranspose_mul_mul_same sp.basis
  simp only [conjTranspose_eq_transpose_of_trivial, sp.diagonalizes] at h
  simpa only [Matrix.diagonal_apply_eq] using psd_diagonal_nonneg h i

def symmetricPowerTrace {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (r : ℝ) : ℝ := ∑ i, ((orderedMatrixSpectrum hA).value i) ^ r

theorem symmetricPowerTrace_eq {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (sp : OrderedMatrixSpectrum A) (r : ℝ) :
    symmetricPowerTrace hA r = ∑ i, sp.value i ^ r := by
  unfold symmetricPowerTrace
  rw [(orderedMatrixSpectrum hA).value_unique sp]

theorem symmetricPowerTrace_one {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) : symmetricPowerTrace hA 1 = A.trace := by
  simp only [symmetricPowerTrace, Real.rpow_one]
  exact (orderedMatrixSpectrum hA).trace.symm

theorem symmetricPowerTrace_nonneg {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (r : ℝ) : 0 ≤ symmetricPowerTrace hA.isHermitian r := by
  exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg
    ((orderedMatrixSpectrum hA.isHermitian).value_nonneg hA i) r)

theorem symmetricPowerTrace_mono {d : ℕ} {A C : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) (hAC : LoewnerLE A C) {r : ℝ} (hr : 0 ≤ r) :
    symmetricPowerTrace hA.isHermitian r ≤ symmetricPowerTrace hC.isHermitian r := by
  apply Finset.sum_le_sum
  intro i _
  exact Real.rpow_le_rpow ((orderedMatrixSpectrum hA.isHermitian).value_nonneg hA i)
    (ordered_eigenvalue_mono _ _ hAC i) hr

theorem rightGram_posSemidef {d t : ℕ} (X : Matrix (Fin d) (Fin t) ℝ) :
    (Xᵀ * X).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self X

def singularValue {d t : ℕ} (X : Matrix (Fin d) (Fin t) ℝ) (i : Fin t) : ℝ :=
  Real.sqrt ((orderedMatrixSpectrum (rightGram_posSemidef X).isHermitian).value i)

def schattenPower {d t : ℕ} (p : ℝ) (X : Matrix (Fin d) (Fin t) ℝ) : ℝ :=
  ∑ i, (singularValue X i) ^ p

def schattenNorm {d t : ℕ} (p : ℝ) (X : Matrix (Fin d) (Fin t) ℝ) : ℝ :=
  (schattenPower p X) ^ (1 / p)

theorem singularValue_nonneg {d t : ℕ} (X : Matrix (Fin d) (Fin t) ℝ) (i : Fin t) :
    0 ≤ singularValue X i := Real.sqrt_nonneg _

theorem schattenPower_nonneg {d t : ℕ} (p : ℝ) (X : Matrix (Fin d) (Fin t) ℝ) :
    0 ≤ schattenPower p X :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (singularValue_nonneg X i) p)

theorem schattenNorm_nonneg {d t : ℕ} (p : ℝ) (X : Matrix (Fin d) (Fin t) ℝ) :
    0 ≤ schattenNorm p X := Real.rpow_nonneg (schattenPower_nonneg p X) _

theorem schattenPower_eq_symmetricPowerTrace {d t : ℕ} (p : ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) :
    schattenPower p X = symmetricPowerTrace (rightGram_posSemidef X).isHermitian (p / 2) := by
  unfold schattenPower symmetricPowerTrace singularValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul
    ((orderedMatrixSpectrum (rightGram_posSemidef X).isHermitian).value_nonneg (rightGram_posSemidef X) i)]
  congr 1
  ring

theorem schattenPower_two {d t : ℕ} (X : Matrix (Fin d) (Fin t) ℝ) :
    schattenPower 2 X = frobeniusSq X := by
  rw [schattenPower_eq_symmetricPowerTrace, div_self (by norm_num : (2 : ℝ) ≠ 0),
    symmetricPowerTrace_one, Matrix.trace_mul_comm, ← frobeniusSq_eq_trace]

theorem schattenNorm_rpow {d t : ℕ} {p : ℝ} (hp : p ≠ 0)
    (X : Matrix (Fin d) (Fin t) ℝ) : (schattenNorm p X) ^ p = schattenPower p X := by
  rw [schattenNorm, ← Real.rpow_mul (schattenPower_nonneg p X), one_div_mul_cancel hp, Real.rpow_one]

end
end LowRank
