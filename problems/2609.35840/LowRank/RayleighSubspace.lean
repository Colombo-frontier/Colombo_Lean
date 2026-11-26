import LowRank.DiagonalInterlacing
import LowRank.SpectralRitzColumns

/-! A lower bound on a Rayleigh quotient throughout a full-column-rank
candidate space gives a lower bound on an ordered eigenvalue. Candidate
columns need not be orthonormal, which allows normalized graph blocks. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem ordered_eigenvalue_lower_of_rayleigh {m k : ℕ} (hk : 0 < k)
    {H : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (sp : OrderedMatrixSpectrum H)
    (F : Matrix (Fin (m + k)) (Fin k) ℝ) (hF : Function.Injective F.mulVec)
    {t : ℝ} (hbound : ∀ x : Fin k → ℝ,
      t * ((F *ᵥ x) ⬝ᵥ (F *ᵥ x)) ≤ (F *ᵥ x) ⬝ᵥ (H *ᵥ (F *ᵥ x))) :
    t ≤ sp.value ⟨m, by omega⟩ := by
  let B := sp.basisᵀ * F
  let r : Fin (k - 1) → Fin (m + k) := fun i => ⟨m + 1 + i.val, by omega⟩
  obtain ⟨x, hx, hx0⟩ := short_matrix_has_nonzero_kernel (k - 1) k (by omega)
    (B.submatrix r id)
  let y := B *ᵥ x
  have hFy : sp.basis *ᵥ y = F *ᵥ x := by
    simp only [y, B, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, sp.orthogonal_right, Matrix.one_mul]
  have hy : ∀ i : Fin (m + k), m < i.val → y i = 0 := by
    intro i hi
    let j : Fin (k - 1) := ⟨i.val - (m + 1), by omega⟩
    have hr : r j = i := by apply Fin.ext; dsimp [r, j]; omega
    have h := congrFun hx j
    change y (r j) = 0 at h
    rwa [hr] at h
  have hFx : F *ᵥ x ≠ 0 := by
    intro h
    apply hx0
    apply hF
    simpa only [Matrix.mulVec_zero] using h
  have hypos : 0 < y ⬝ᵥ y := by
    have hnorm := orthogonal_columns_dot sp.basis sp.orthogonal y
    rw [hFy] at hnorm
    rw [← hnorm]
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hFx)
  have hl := hbound x
  rw [← hFy, orthogonal_columns_dot sp.basis sp.orthogonal, sp.quadratic] at hl
  have hu : (∑ i, sp.value i * y i ^ 2) ≤ sp.value ⟨m, by omega⟩ * (y ⬝ᵥ y) := by
    rw [dot_self_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : m < i.val
    · simp only [hy i hi, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (sp.increasing (by exact Nat.le_of_not_gt hi)) (sq_nonneg _)
  exact (mul_le_mul_right hypos).mp (hl.trans hu)

theorem ordered_eigenvalue_lower_of_gram_loewner {m k : ℕ} (hk : 0 < k)
    {H : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (sp : OrderedMatrixSpectrum H)
    (F : Matrix (Fin (m + k)) (Fin k) ℝ) (hF : Function.Injective F.mulVec)
    {t : ℝ} (hbound : LoewnerLE (t • (Fᵀ * F)) (Fᵀ * H * F)) :
    t ≤ sp.value ⟨m, by omega⟩ := by
  apply ordered_eigenvalue_lower_of_rayleigh hk sp F hF
  intro x
  have h := loewner_quadratic_le hbound x
  rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul] at h
  have hn := quadratic_coordinates F (1 : Matrix (Fin (m + k)) (Fin (m + k)) ℝ) x
  simp only [Matrix.one_mulVec, Matrix.mul_one] at hn
  rw [← hn, ← quadratic_coordinates] at h
  exact h

theorem compressed_gram_eigenvalue_lower_of_candidate {a m k : ℕ} (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ)
    {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ}
    (F : Matrix (Fin (m + k)) (Fin k) ℝ) (hF : Function.Injective F.mulVec)
    (hfix : P * F = F) {t : ℝ}
    (hbound : ∀ x : Fin k → ℝ, t * ((F *ᵥ x) ⬝ᵥ (F *ᵥ x)) ≤
      (A *ᵥ (F *ᵥ x)) ⬝ᵥ (A *ᵥ (F *ᵥ x))) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A * P))).value ⟨m, by omega⟩ := by
  apply ordered_eigenvalue_lower_of_rayleigh hk _ F hF
  intro x
  have hp : (A * P) *ᵥ (F *ᵥ x) = A *ᵥ (F *ᵥ x) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hfix]
  have he := quadratic_coordinates (A * P) (1 : Matrix (Fin a) (Fin a) ℝ) (F *ᵥ x)
  simp only [Matrix.one_mulVec, Matrix.mul_one, hp] at he
  change t * ((F *ᵥ x) ⬝ᵥ (F *ᵥ x)) ≤
    (F *ᵥ x) ⬝ᵥ (((A * P)ᵀ * (A * P)) *ᵥ (F *ᵥ x))
  rw [← he]
  exact hbound x

theorem ordered_eigenvalue_lower_of_rayleigh_of_le {d r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ d) {H : Matrix (Fin d) (Fin d) ℝ} (sp : OrderedMatrixSpectrum H)
    (F : Matrix (Fin d) (Fin r) ℝ) (hF : Function.Injective F.mulVec)
    {t : ℝ} (hbound : ∀ x : Fin r → ℝ,
      t * ((F *ᵥ x) ⬝ᵥ (F *ᵥ x)) ≤ (F *ᵥ x) ⬝ᵥ (H *ᵥ (F *ᵥ x))) :
    t ≤ sp.value (lastColumnIndex d r hr ⟨0, hr0⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hr
  simpa only [lastColumnIndex_add, Fin.natAdd_mk, Nat.add_zero] using
    ordered_eigenvalue_lower_of_rayleigh hr0 sp F hF hbound

theorem compressed_gram_eigenvalue_lower_of_candidate_of_le {a d r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ d) (A : Matrix (Fin a) (Fin d) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (F : Matrix (Fin d) (Fin r) ℝ)
    (hF : Function.Injective F.mulVec) (hfix : P * F = F) {t : ℝ}
    (hbound : ∀ x : Fin r → ℝ, t * ((F *ᵥ x) ⬝ᵥ (F *ᵥ x)) ≤
      (A *ᵥ (F *ᵥ x)) ⬝ᵥ (A *ᵥ (F *ᵥ x))) :
    t ≤ (canonicalOrderedSpectrum d (symmetricRightGram (A * P))).value
      (lastColumnIndex d r hr ⟨0, hr0⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hr
  simpa only [lastColumnIndex_add, Fin.natAdd_mk, Nat.add_zero] using
    compressed_gram_eigenvalue_lower_of_candidate hr0 A F hF hfix hbound

end
end LowRank
