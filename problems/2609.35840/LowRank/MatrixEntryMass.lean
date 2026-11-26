import LowRank.GramSpectrum

/-! An elementary continuous entrywise bound for symmetric perturbations.
No identification of the ambient matrix norm with a Euclidean operator norm
is needed. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def matrixEntryMass {d t : ℕ} (A : Matrix (Fin d) (Fin t) ℝ) : ℝ := ∑ i, ∑ j, |A i j|

theorem matrixEntryMass_nonneg {d t : ℕ} (A : Matrix (Fin d) (Fin t) ℝ) :
    0 ≤ matrixEntryMass A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem matrixEntryMass_zero (d t : ℕ) :
    matrixEntryMass (0 : Matrix (Fin d) (Fin t) ℝ) = 0 := by simp [matrixEntryMass]

theorem matrixEntryMass_sub_comm {d t : ℕ} (A B : Matrix (Fin d) (Fin t) ℝ) :
    matrixEntryMass (A - B) = matrixEntryMass (B - A) := by
  simp only [matrixEntryMass, Matrix.sub_apply, abs_sub_comm]

theorem continuous_matrixEntryMass (d t : ℕ) :
    Continuous (matrixEntryMass : Matrix (Fin d) (Fin t) ℝ → ℝ) := by
  unfold matrixEntryMass
  fun_prop

theorem quadratic_le_matrixEntryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : x ⬝ᵥ (A *ᵥ x) ≤ matrixEntryMass A * (x ⬝ᵥ x) := by
  have hsq (i : Fin d) : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hpair (i j : Fin d) : |x i| * |x j| ≤ ∑ l, x l ^ 2 := by
    nlinarith [hsq i, hsq j, sq_abs (x i), sq_abs (x j), sq_nonneg (|x i| - |x j|)]
  have hterm (i j : Fin d) : x i * (A i j * x j) ≤ |A i j| * (∑ l, x l ^ 2) := by
    calc
      _ ≤ |x i * (A i j * x j)| := le_abs_self _
      _ = |A i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpair i j) (abs_nonneg _)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j))
  calc
    _ = ∑ i, ∑ j, x i * (A i j * x j) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |A i j| * (∑ l, x l ^ 2) := h
    _ = _ := by simp only [← Finset.sum_mul, matrixEntryMass, dot_self_eq_sum_sq]

theorem symmetric_le_matrixEntryMass {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) : LoewnerLE A (matrixEntryMass A • 1) := by
  constructor
  · change (matrixEntryMass A • 1 - A)ᴴ = matrixEntryMass A • 1 - A
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, hA.eq]
  · intro x
    have h := quadratic_le_matrixEntryMass A x
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg] using h

theorem loewner_le_shift_entryMass {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    LoewnerLE A (B + matrixEntryMass (A - B) • 1) := by
  have h := symmetric_le_matrixEntryMass (hA.sub hB)
  change (matrixEntryMass (A - B) • 1 - (A - B)).PosSemidef at h
  change (B + matrixEntryMass (A - B) • 1 - A).PosSemidef
  convert h using 1
  abel

end
end LowRank
