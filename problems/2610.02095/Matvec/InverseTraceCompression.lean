import LowRank.UpperMatrixInterlacing
import LowRank.InverseGramWishartBound
import Mathlib.Tactic

/-! Deterministic inverse-trace comparison with a fixed-codimension
compression. Used to establish a positive square-Gaussian low event. -/
namespace Matvec
open Matrix LowRank
open scoped Matrix BigOperators
noncomputable section

theorem inverse_diagonalizes {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (sp : OrderedMatrixSpectrum A) (hval : ∀ i, sp.value i ≠ 0) :
    sp.basisᵀ * A⁻¹ * sp.basis = Matrix.diagonal (fun i => (sp.value i)⁻¹) := by
  have hU : sp.basis⁻¹ = sp.basisᵀ := Matrix.inv_eq_left_inv sp.orthogonal
  have hUt : sp.basisᵀ⁻¹ = sp.basis := Matrix.inv_eq_right_inv sp.orthogonal
  have h := congrArg Inv.inv sp.diagonalizes
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hU, hUt, Matrix.inv_diagonal] at h
  have hu : IsUnit sp.value := by
    refine ⟨⟨sp.value, (fun i => (sp.value i)⁻¹), ?_, ?_⟩, rfl⟩
    · ext i; exact mul_inv_cancel₀ (hval i)
    · ext i; exact inv_mul_cancel₀ (hval i)
  have hinv : Ring.inverse sp.value = fun i => (sp.value i)⁻¹ := by
    funext i
    have hm := congrFun (Ring.mul_inverse_cancel _ hu) i
    change sp.value i * Ring.inverse sp.value i = 1 at hm
    apply mul_left_cancel₀ (hval i)
    rw [hm, mul_inv_cancel₀ (hval i)]
  rw [hinv] at h
  simpa only [Matrix.mul_assoc] using h

theorem inverse_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (sp : OrderedMatrixSpectrum A) (hval : ∀ i, sp.value i ≠ 0) :
    A⁻¹.trace = ∑ i, (sp.value i)⁻¹ := by
  have h := congrArg Matrix.trace (inverse_diagonalizes sp hval)
  rw [Matrix.trace_mul_cycle, sp.orthogonal_right, Matrix.one_mul,
    Matrix.trace_diagonal] at h
  exact h

theorem inverse_eigenvalue_le_of_loewner {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (sp : OrderedMatrixSpectrum A) (hval : ∀ i, sp.value i ≠ 0)
    (L : ℝ) (hL : LoewnerLE A⁻¹ (L • 1))
    (i : Fin n) : (sp.value i)⁻¹ ≤ L := by
  have h := loewner_congruence hL sp.basis
  simp only [inverse_diagonalizes sp hval, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, sp.orthogonal] at h
  have hd := psd_diagonal_nonneg h i
  simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.diagonal_apply_eq, sub_nonneg] using hd

theorem inverse_trace_compression_le {r m : ℕ}
    {A : Matrix (Fin (r + m)) (Fin (r + m)) ℝ}
    {C : Matrix (Fin m) (Fin m) ℝ}
    (spA : OrderedMatrixSpectrum A) (spC : OrderedMatrixSpectrum C)
    (B : Matrix (Fin (r + m)) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hcomp : Bᵀ * A * B = C) (hAval : ∀ i, spA.value i ≠ 0)
    (hCpos : ∀ i, 0 < spC.value i)
    (L : ℝ) (hL : LoewnerLE A⁻¹ (L • 1)) :
    A⁻¹.trace ≤ r * L + C⁻¹.trace := by
  rw [inverse_trace spA hAval, inverse_trace spC (fun i => (hCpos i).ne'), Fin.sum_univ_add]
  apply add_le_add
  · calc
      _ ≤ ∑ _ : Fin r, L := Finset.sum_le_sum fun i _ =>
        inverse_eigenvalue_le_of_loewner spA hAval L hL _
      _ = _ := by simp
  · apply Finset.sum_le_sum
    intro i _
    have h := ordered_compression_eigenvalue_le_upper (Nat.le_add_left m r)
      spA spC B hB hcomp i
    have he : (i.rev.castLE (Nat.le_add_left m r)).rev = i.natAdd r := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.coe_castLE, Fin.coe_natAdd]
      omega
    rw [he] at h
    exact inv_anti₀ (hCpos i) h

end
end Matvec
