import LowRank.PositiveSpectralLeftColumns

/-! Enumerate only the positive Gram eigenvalues. Zero eigenvalues give
zero matrix columns in spectral coordinates, including rank-deficient inputs. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def positiveSpectrumSize {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) : ℕ :=
  Fintype.card {i : Fin d // 0 < sp.value i}

def positiveSpectrumIndex {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) : Fin (positiveSpectrumSize sp) → Fin d :=
  fun j => ((Fintype.equivFin {i : Fin d // 0 < sp.value i}).symm j).val

theorem positiveSpectrumIndex_injective {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) : Function.Injective (positiveSpectrumIndex sp) :=
  Subtype.val_injective.comp (Fintype.equivFin {i : Fin d // 0 < sp.value i}).symm.injective

theorem positiveSpectrumIndex_positive {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) (j : Fin (positiveSpectrumSize sp)) :
    0 < sp.value (positiveSpectrumIndex sp j) :=
  ((Fintype.equivFin {i : Fin d // 0 < sp.value i}).symm j).property

theorem positiveSpectrumIndex_covers {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) (i : Fin d) (hi : 0 < sp.value i) :
    ∃ j, positiveSpectrumIndex sp j = i := by
  refine ⟨(Fintype.equivFin {i : Fin d // 0 < sp.value i}) ⟨i, hi⟩, ?_⟩
  simp [positiveSpectrumIndex]

theorem positiveSpectrumSize_le_of_zero_tail {a m k : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hz : ∀ i : Fin m, sp.value (i.castAdd k) = 0) : positiveSpectrumSize sp ≤ k := by
  have hge (i : {i : Fin (m + k) // 0 < sp.value i}) : m ≤ i.val.val := by
    by_contra! h
    have he : (⟨i.val.val, h⟩ : Fin m).castAdd k = i.val := by ext; rfl
    have hv := hz ⟨i.val.val, h⟩
    rw [he] at hv
    have hp := i.property
    linarith
  let g : {i : Fin (m + k) // 0 < sp.value i} → Fin k :=
    fun i => ⟨i.val.val - m, by have hi := i.val.isLt; have hm := hge i; omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have h := congrArg Fin.val hij
    change i.val.val - m = j.val.val - m at h
    have hi := hge i
    have hj := hge j
    omega
  have h := Fintype.card_le_of_injective g hg
  simpa only [positiveSpectrumSize, Fintype.card_fin] using h

theorem spectral_image_column_zero {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (i : Fin b) (hi : sp.value i = 0) :
    ∀ j : Fin a, (A * sp.basis) j i = 0 := by
  have he : (A * sp.basis)ᵀ * (A * sp.basis) = diagonal sp.value := by
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using sp.diagonalizes
  have h := congrFun (congrFun he i) i
  have hs : ∑ j : Fin a, ((A * sp.basis) j i) ^ 2 = 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply_eq, hi, pow_two] using h
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((A * sp.basis) j i))).mp hs
    j (Finset.mem_univ j)
  exact pow_eq_zero hj

theorem spectral_support_reconstruct {a b r : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin r → Fin b) (hf : Function.Injective f)
    (hcover : ∀ i : Fin b, 0 < sp.value i → ∃ j, f j = i) :
    Aᵀ = sp.basis.submatrix id f * (A * sp.basis.submatrix id f)ᵀ := by
  have hfull : Aᵀ = sp.basis * (A * sp.basis)ᵀ := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, sp.orthogonal_right, Matrix.one_mul]
  refine hfull.trans ?_
  ext i j
  change (∑ l : Fin b, sp.basis i l * (A * sp.basis) j l) =
    ∑ l : Fin r, sp.basis i (f l) * (A * sp.basis) j (f l)
  calc
    _ = ∑ l ∈ Finset.univ.image f, sp.basis i l * (A * sp.basis) j l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      have hv : sp.value l = 0 := by
        have hn : ¬0 < sp.value l := by
          intro hp
          obtain ⟨x, hx⟩ := hcover l hp
          exact hl (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
        exact le_antisymm (le_of_not_gt hn) (sp.value_nonneg (rightGram_posSemidef A) l)
      rw [spectral_image_column_zero A sp l hv j, mul_zero]
    _ = _ := by
      rw [Finset.sum_image]
      intro x _ y _ h
      exact hf h

end
end LowRank
