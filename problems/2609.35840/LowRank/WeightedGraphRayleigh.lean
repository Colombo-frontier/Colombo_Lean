import LowRank.RayleighSubspace
import LowRank.WeightedFilteredApproximation

/-! Graph candidates only lose Rayleigh energy on eigenvalues below the
target threshold. The deficit-weighted tail norm allows nearby spectral
directions without demanding that the entire tail block be small. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def weightedFrobeniusSq {m k : ℕ} (w : Fin m → ℝ) (L : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  ∑ i, w i * ∑ j, L i j ^ 2

theorem weightedFrobeniusSq_nonneg {m k : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (L : Matrix (Fin m) (Fin k) ℝ) :
    0 ≤ weightedFrobeniusSq w L :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem weighted_mulVec_sq_le {m k : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    (∑ i, w i * (L *ᵥ x) i ^ 2) ≤ weightedFrobeniusSq w L * (x ⬝ᵥ x) := by
  rw [weightedFrobeniusSq, Finset.sum_mul, dot_self_eq_sum_sq]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => L i j) x) (hw i)

theorem weightedFrobeniusSq_eq_sqrt_diagonal {m k : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (L : Matrix (Fin m) (Fin k) ℝ) :
    weightedFrobeniusSq w L = frobeniusSq (diagonal (fun i => Real.sqrt (w i)) * L) := by
  simp only [weightedFrobeniusSq, frobeniusSq, Matrix.diagonal_mul, mul_pow,
    Real.sq_sqrt (hw _), Finset.mul_sum]

theorem graphBlock_head_mulVec {m k : ℕ} (Y : Matrix (Fin (m + k)) (Fin k) ℝ)
    (hhead : Y.submatrix (Fin.natAdd m) id = 1) (x : Fin k → ℝ) (j : Fin k) :
    (Y *ᵥ x) (j.natAdd m) = x j := by
  have h := congrArg (fun M => M *ᵥ x) hhead
  simpa only [Matrix.one_mulVec] using congrFun h j

theorem graphBlock_mulVec_injective {d m k : ℕ}
    (V : Matrix (Fin d) (Fin (m + k)) ℝ) (hV : Vᵀ * V = 1)
    (Y : Matrix (Fin (m + k)) (Fin k) ℝ) (hhead : Y.submatrix (Fin.natAdd m) id = 1) :
    Function.Injective (V * Y).mulVec := by
  intro x z hxz
  have h := congrArg (fun v => Vᵀ *ᵥ v) hxz
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hV, Matrix.one_mul] at h
  funext j
  have hj := congrFun h (j.natAdd m)
  simpa only [graphBlock_head_mulVec Y hhead] using hj

theorem graphBlock_rayleigh_lower {m k : ℕ}
    {H : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (sp : OrderedMatrixSpectrum H)
    (Y : Matrix (Fin (m + k)) (Fin k) ℝ) (hhead : Y.submatrix (Fin.natAdd m) id = 1)
    {t α : ℝ} (hh : ∀ j : Fin k, α ≤ sp.value (j.natAdd m))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (Y.submatrix (Fin.castAdd k) id) ≤ α - t) (x : Fin k → ℝ) :
    t * (((sp.basis * Y) *ᵥ x) ⬝ᵥ ((sp.basis * Y) *ᵥ x)) ≤
      ((sp.basis * Y) *ᵥ x) ⬝ᵥ (H *ᵥ ((sp.basis * Y) *ᵥ x)) := by
  let z := Y *ᵥ x
  have hn : (((sp.basis * Y) *ᵥ x) ⬝ᵥ ((sp.basis * Y) *ᵥ x)) =
      (∑ i : Fin m, z (i.castAdd k) ^ 2) + x ⬝ᵥ x := by
    rw [← Matrix.mulVec_mulVec, orthogonal_columns_dot sp.basis sp.orthogonal,
      dot_self_eq_sum_sq, Fin.sum_univ_add]
    simp only [z, graphBlock_head_mulVec Y hhead, dot_self_eq_sum_sq]
  have he : ((sp.basis * Y) *ᵥ x) ⬝ᵥ (H *ᵥ ((sp.basis * Y) *ᵥ x)) =
      (∑ i : Fin m, sp.value (i.castAdd k) * z (i.castAdd k) ^ 2) +
        ∑ j : Fin k, sp.value (j.natAdd m) * x j ^ 2 := by
    rw [← Matrix.mulVec_mulVec, sp.quadratic, Fin.sum_univ_add]
    simp only [z, graphBlock_head_mulVec Y hhead]
  have ht : t * (∑ i : Fin m, z (i.castAdd k) ^ 2) -
      (∑ i : Fin m, sp.value (i.castAdd k) * z (i.castAdd k) ^ 2) ≤
        weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
          (Y.submatrix (Fin.castAdd k) id) * (x ⬝ᵥ x) := by
    calc
      _ = ∑ i : Fin m, (t - sp.value (i.castAdd k)) * z (i.castAdd k) ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i : Fin m, max 0 (t - sp.value (i.castAdd k)) * z (i.castAdd k) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      _ ≤ _ := weighted_mulVec_sq_le _ (fun _ => le_max_left _ _) _ x
  have hhx : α * (x ⬝ᵥ x) ≤ ∑ j : Fin k, sp.value (j.natAdd m) * x j ^ 2 := by
    rw [dot_self_eq_sum_sq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hh j) (sq_nonneg _))
  have hxx : 0 ≤ x ⬝ᵥ x := by
    rw [dot_self_eq_sum_sq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hbudget hxx
  rw [hn, he]
  nlinarith

end
end LowRank
