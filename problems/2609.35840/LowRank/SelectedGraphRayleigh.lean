import LowRank.WeightedGraphRayleigh

/-! A graph block may retain an isometric selection of the full head
coordinates. Unselected head rows are exactly zero for coordinate columns,
so their eigenvalues do not enter the tail error budget. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def coordinateColumns {k r : ℕ} (f : Fin r → Fin k) : Matrix (Fin k) (Fin r) ℝ :=
  (1 : Matrix (Fin k) (Fin k) ℝ).submatrix id f

theorem coordinateColumns_orthogonal {k r : ℕ} (f : Fin r → Fin k) (hf : Function.Injective f) :
    (coordinateColumns f)ᵀ * coordinateColumns f = 1 :=
  orthogonal_subcolumns 1 (by simp) f hf

theorem coordinateColumns_diagonal_compression {k r : ℕ}
    (f : Fin r → Fin k) (hf : Function.Injective f) (lam : Fin k → ℝ) :
    (coordinateColumns f)ᵀ * diagonal lam * coordinateColumns f = diagonal (lam ∘ f) := by
  rw [coordinateColumns, compressed_submatrix]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_diagonal _ _ hf]

theorem graphBlock_isometric_head_mulVec {m k r : ℕ}
    (Y : Matrix (Fin (m + k)) (Fin r) ℝ) (E : Matrix (Fin k) (Fin r) ℝ)
    (hhead : Y.submatrix (Fin.natAdd m) id = E) (x : Fin r → ℝ) (j : Fin k) :
    (Y *ᵥ x) (j.natAdd m) = (E *ᵥ x) j :=
  congrFun (congrArg (fun M => M *ᵥ x) hhead) j

theorem graphBlock_isometric_head_injective {d m k r : ℕ}
    (V : Matrix (Fin d) (Fin (m + k)) ℝ) (hV : Vᵀ * V = 1)
    (Y : Matrix (Fin (m + k)) (Fin r) ℝ) (E : Matrix (Fin k) (Fin r) ℝ)
    (hE : Eᵀ * E = 1) (hhead : Y.submatrix (Fin.natAdd m) id = E) :
    Function.Injective (V * Y).mulVec := by
  intro x z hxz
  have h := congrArg (fun v => Vᵀ *ᵥ v) hxz
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hV, Matrix.one_mul] at h
  have hh : E *ᵥ x = E *ᵥ z := by
    funext j
    simpa only [graphBlock_isometric_head_mulVec Y E hhead] using congrFun h (j.natAdd m)
  have he := congrArg (fun v => Eᵀ *ᵥ v) hh
  simpa only [Matrix.mulVec_mulVec, hE, Matrix.one_mulVec] using he

theorem graphBlock_isometric_head_rayleigh_lower {m k r : ℕ}
    {H : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (sp : OrderedMatrixSpectrum H)
    (Y : Matrix (Fin (m + k)) (Fin r) ℝ) (E : Matrix (Fin k) (Fin r) ℝ)
    (hE : Eᵀ * E = 1) (hhead : Y.submatrix (Fin.natAdd m) id = E)
    {t α : ℝ} (hh : LoewnerLE (α • 1) (Eᵀ * diagonal (fun j : Fin k => sp.value (j.natAdd m)) * E))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (Y.submatrix (Fin.castAdd k) id) ≤ α - t) (x : Fin r → ℝ) :
    t * (((sp.basis * Y) *ᵥ x) ⬝ᵥ ((sp.basis * Y) *ᵥ x)) ≤
      ((sp.basis * Y) *ᵥ x) ⬝ᵥ (H *ᵥ ((sp.basis * Y) *ᵥ x)) := by
  let z := Y *ᵥ x
  have hn : (((sp.basis * Y) *ᵥ x) ⬝ᵥ ((sp.basis * Y) *ᵥ x)) =
      (∑ i : Fin m, z (i.castAdd k) ^ 2) + x ⬝ᵥ x := by
    rw [← Matrix.mulVec_mulVec, orthogonal_columns_dot sp.basis sp.orthogonal,
      dot_self_eq_sum_sq, Fin.sum_univ_add]
    simp only [z, graphBlock_isometric_head_mulVec Y E hhead]
    rw [← dot_self_eq_sum_sq (E *ᵥ x), orthogonal_columns_dot E hE]
  have he : ((sp.basis * Y) *ᵥ x) ⬝ᵥ (H *ᵥ ((sp.basis * Y) *ᵥ x)) =
      (∑ i : Fin m, sp.value (i.castAdd k) * z (i.castAdd k) ^ 2) +
        (E *ᵥ x) ⬝ᵥ (diagonal (fun j : Fin k => sp.value (j.natAdd m)) *ᵥ (E *ᵥ x)) := by
    rw [← Matrix.mulVec_mulVec, sp.quadratic, Fin.sum_univ_add, diagonal_quadratic]
    simp only [z, graphBlock_isometric_head_mulVec Y E hhead]
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
  have hhx := loewner_quadratic_le hh x
  rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    ← quadratic_coordinates] at hhx
  have hxx : 0 ≤ x ⬝ᵥ x := by
    rw [dot_self_eq_sum_sq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hbudget hxx
  rw [hn, he]
  nlinarith

theorem selected_graph_ritz_lower {a m k r : ℕ} (hr0 : 0 < r) (hr : r ≤ m + k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ}
    (Y : Matrix (Fin (m + k)) (Fin r) ℝ) (f : Fin r → Fin k) (hf : Function.Injective f)
    (hhead : Y.submatrix (Fin.natAdd m) id = coordinateColumns f)
    (hfix : P * (sp.basis * Y) = sp.basis * Y) {t α : ℝ}
    (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m))
    (hbudget : weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      (Y.submatrix (Fin.castAdd k) id) ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A * P))).value
      (lastColumnIndex (m + k) r hr ⟨0, hr0⟩) := by
  have hE := coordinateColumns_orthogonal f hf
  apply compressed_gram_eigenvalue_lower_of_candidate_of_le hr0 hr A (sp.basis * Y)
    (graphBlock_isometric_head_injective sp.basis sp.orthogonal Y _ hE hhead) hfix
  intro x
  have hdiag : LoewnerLE (α • 1)
      ((coordinateColumns f)ᵀ * diagonal (fun j : Fin k => sp.value (j.natAdd m)) * coordinateColumns f) := by
    rw [coordinateColumns_diagonal_compression f hf, LoewnerLE,
      ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun j => by simpa using sub_nonneg.mpr (hh j))
  have h := graphBlock_isometric_head_rayleigh_lower sp Y _ hE hhead hdiag hbudget x
  have he := quadratic_coordinates A (1 : Matrix (Fin a) (Fin a) ℝ) ((sp.basis * Y) *ᵥ x)
  simp only [Matrix.one_mulVec, Matrix.mul_one] at he
  rw [he]
  exact h

end
end LowRank
