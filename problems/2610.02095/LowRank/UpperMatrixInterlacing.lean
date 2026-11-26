import LowRank.SpectralCompression
import Mathlib.Data.Fin.Rev

/-! The other half of Poincare separation, and contraction of positive
spectral power sums under compression by orthonormal columns. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def OrderedMatrixSpectrum.neg {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) : OrderedMatrixSpectrum (-A) := by
  let e : Equiv.Perm (Fin d) := Fin.revPerm
  refine ⟨fun i => -sp.value i.rev, sp.basis.submatrix id e, ?_, ?_, ?_⟩
  · intro i j hij
    exact neg_le_neg (sp.increasing (Fin.rev_le_rev.mpr hij))
  · change sp.basisᵀ.submatrix e id * sp.basis.submatrix id e = 1
    have h := Matrix.submatrix_mul_equiv sp.basisᵀ sp.basis e (Equiv.refl (Fin d)) e
    simpa only [Equiv.coe_refl, sp.orthogonal, Matrix.submatrix_one_equiv] using h
  · change sp.basisᵀ.submatrix e id * (-A) * sp.basis.submatrix id e = _
    have hfirst : sp.basisᵀ.submatrix e id * (-A) = (sp.basisᵀ * (-A)).submatrix e id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv sp.basisᵀ (-A) e (Equiv.refl (Fin d)) id
    rw [hfirst]
    have h := Matrix.submatrix_mul_equiv (sp.basisᵀ * (-A)) sp.basis e (Equiv.refl (Fin d)) e
    simpa only [Equiv.coe_refl, Matrix.mul_neg, Matrix.neg_mul, sp.diagonalizes,
      Matrix.submatrix_neg, Pi.neg_apply, Matrix.submatrix_diagonal_equiv,
      ← Matrix.diagonal_neg] using h

theorem ordered_compression_eigenvalue_le_upper {d m : ℕ} (hm : m ≤ d)
    {A : Matrix (Fin d) (Fin d) ℝ} {C : Matrix (Fin m) (Fin m) ℝ}
    (spA : OrderedMatrixSpectrum A) (spC : OrderedMatrixSpectrum C)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hcomp : Bᵀ * A * B = C) (i : Fin m) :
    spC.value i ≤ spA.value ((i.rev.castLE hm).rev) := by
  have h := ordered_compression_eigenvalue_le hm spA.neg spC.neg B hB
    (by simpa only [Matrix.mul_neg, Matrix.neg_mul] using congrArg Neg.neg hcomp) i.rev
  simpa only [OrderedMatrixSpectrum.neg, Fin.rev_rev, neg_le_neg_iff] using h

theorem compression_power_le_total {d m : ℕ} (hm : m ≤ d)
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) {r : ℝ} (hr : 0 ≤ r) :
    symmetricPowerTrace (compression_isHermitian hA.isHermitian B) r ≤
      symmetricPowerTrace hA.isHermitian r := by
  let spA := orderedMatrixSpectrum hA.isHermitian
  let spC := orderedMatrixSpectrum (compression_isHermitian hA.isHermitian B)
  have hC : (Bᵀ * A * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_mul_same B
  let e : Fin m → Fin d := fun i => (i.rev.castLE hm).rev
  have he : Function.Injective e := Fin.rev_injective.comp
    ((Fin.castLE_injective hm).comp Fin.rev_injective)
  calc
    _ ≤ ∑ i : Fin m, spA.value (e i) ^ r := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (spC.value_nonneg hC i)
        (ordered_compression_eigenvalue_le_upper hm spA spC B hB rfl i) hr
    _ = ∑ j ∈ Finset.univ.image e, spA.value j ^ r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => he h
    _ ≤ symmetricPowerTrace hA.isHermitian r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Real.rpow_nonneg (spA.value_nonneg hA i) r

end
end LowRank
