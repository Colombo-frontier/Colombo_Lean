import LowRank.SelectedGraphRayleigh
import LowRank.FilteredRitzLower

/-! Select target columns after inverting the entire head starting block.
The resulting head is a coordinate embedding, so unselected head rows
vanish exactly and the weighted error uses only the original tail. -/

namespace LowRank
open Matrix Polynomial
open scoped Matrix BigOperators
noncomputable section

def selectedNormalizedFilteredBlock {m k s r : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (f : Fin r → Fin k) : Matrix (Fin (m + k)) (Fin r) ℝ :=
  diagonal w * (B * R.submatrix id f) * diagonal (fun j => (w ((f j).natAdd m))⁻¹)

def selectedFilteredTailBlock {m k s r : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (f : Fin r → Fin k) : Matrix (Fin m) (Fin r) ℝ :=
  diagonal (fun i => w (i.castAdd k)) * (B.submatrix (Fin.castAdd k) id * R.submatrix id f) *
    diagonal (fun j => (w ((f j).natAdd m))⁻¹)

theorem selectedNormalizedFilteredBlock_head {m k s r : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (f : Fin r → Fin k) (hR : B.submatrix (Fin.natAdd m) id * R = 1)
    (hw : ∀ j : Fin r, w ((f j).natAdd m) ≠ 0) :
    (selectedNormalizedFilteredBlock w B R f).submatrix (Fin.natAdd m) id = coordinateColumns f := by
  ext i j
  have h := congrFun (congrFun hR i) (f j)
  change (B * R) (i.natAdd m) (f j) = (1 : Matrix (Fin k) (Fin k) ℝ) i (f j) at h
  have hsub : B * R.submatrix id f = (B * R).submatrix id f := by ext l j; rfl
  simp only [selectedNormalizedFilteredBlock, coordinateColumns, hsub, Matrix.submatrix_apply,
    id_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, h]
  change w (i.natAdd m) * (1 : Matrix (Fin k) (Fin k) ℝ) i (f j) *
    (w ((f j).natAdd m))⁻¹ = (1 : Matrix (Fin k) (Fin k) ℝ) i (f j)
  by_cases hij : i = f j
  · rw [hij]
    simp only [id_eq, Matrix.one_apply_eq, mul_one, mul_inv_cancel₀ (hw j)]
  · simp only [id_eq, Matrix.one_apply_ne hij, mul_zero, zero_mul]

theorem selectedNormalizedFilteredBlock_tail {m k s r : ℕ} (w : Fin (m + k) → ℝ)
    (B : Matrix (Fin (m + k)) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ) (f : Fin r → Fin k) :
    (selectedNormalizedFilteredBlock w B R f).submatrix (Fin.castAdd k) id = selectedFilteredTailBlock w B R f := by
  ext i j
  simp only [selectedNormalizedFilteredBlock, selectedFilteredTailBlock, Matrix.submatrix_apply,
    id_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem selectedFilteredTailBlock_deficit_bound {m k s r : ℕ}
    (lam w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) (f : Fin r → Fin k) {t η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i : Fin m, lam (i.castAdd k) < t → |w (i.castAdd k)| ≤ η)
    (hh : ∀ j : Fin r, 1 ≤ w ((f j).natAdd m)) :
    weightedFrobeniusSq (fun i : Fin m => max 0 (t - lam (i.castAdd k)))
      (selectedFilteredTailBlock w B R f) ≤
        η ^ 2 * weightedFrobeniusSq (fun i : Fin m => max 0 (t - lam (i.castAdd k)))
          (B.submatrix (Fin.castAdd k) id * R.submatrix id f) := by
  apply weightedFrobeniusSq_diagonal_sandwich_le _ (fun _ => le_max_left _ _) _ _ _ hη
  · intro i hi
    apply hl i
    rcases lt_max_iff.mp hi with h | h
    · exact (lt_irrefl _ h).elim
    · linarith
  · intro j
    rw [abs_inv, abs_of_nonneg (by linarith [hh j] : 0 ≤ w ((f j).natAdd m))]
    exact inv_le_one_of_one_le₀ (hh j)

theorem selected_filtered_ritz_lower_of_deficit {a m k s r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + k) (A : Matrix (Fin a) (Fin (m + k)) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ}
    (w : Fin (m + k) → ℝ) (B : Matrix (Fin (m + k)) (Fin s) ℝ)
    (R : Matrix (Fin s) (Fin k) ℝ) (f : Fin r → Fin k) (hf : Function.Injective f)
    (hR : B.submatrix (Fin.natAdd m) id * R = 1)
    (hw : ∀ j : Fin r, w ((f j).natAdd m) ≠ 0)
    (hfix : P * (sp.basis * (diagonal w * B)) = sp.basis * (diagonal w * B))
    {t α : ℝ} (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (selectedFilteredTailBlock w B R f) ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A * P))).value
      (lastColumnIndex (m + k) r hr ⟨0, hr0⟩) := by
  refine selected_graph_ritz_lower hr0 hr A sp (selectedNormalizedFilteredBlock w B R f) f hf
    (selectedNormalizedFilteredBlock_head w B R f hR hw) ?_ hh ?_
  · have h := congrArg (fun M => M * R.submatrix id f * diagonal (fun j => (w ((f j).natAdd m))⁻¹)) hfix
    simpa only [selectedNormalizedFilteredBlock, Matrix.mul_assoc] using h
  · simpa only [selectedNormalizedFilteredBlock_tail] using hbudget

theorem krylov_selected_ritz_lower_of_deficit {a m k s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + k) (A : Matrix (Fin a) (Fin (m + k)) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (q : ℝ[X]) (hq : q.natDegree < n) (R : Matrix (Fin s) (Fin k) ℝ)
    (f : Fin r → Fin k) (hf : Function.Injective f)
    (hR : (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id * R = 1)
    (hw : ∀ j : Fin r, q.eval (sp.value ((f j).natAdd m)) ≠ 0)
    {t α : ℝ} (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (selectedFilteredTailBlock (fun i => q.eval (sp.value i)) (sp.basisᵀ * (Aᵀ * U)) R f) ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + k) r hr ⟨0, hr0⟩) := by
  apply selected_filtered_ritz_lower_of_deficit hr0 hr A sp (fun i => q.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) R f hf hR hw _ hh hbudget
  have heq : aeval (Aᵀ * A) q * (Aᵀ * U) =
      sp.basis * (diagonal (fun i => q.eval (sp.value i)) * (sp.basisᵀ * (Aᵀ * U))) := by
    rw [sp.aeval_reconstruct q]
    simp only [Matrix.mul_assoc]
  rw [← heq]
  exact krylovProjector_fixes_aeval A U q hq

end
end LowRank
