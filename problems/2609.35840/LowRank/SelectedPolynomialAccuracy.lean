import LowRank.SelectedGapAccuracy

/-! A selected Ritz lower bound from any available polynomial filter.
Only deficit directions require attenuation; all low eigenvalues bound energy. -/

namespace LowRank
open Matrix Polynomial
open scoped Matrix BigOperators
noncomputable section

theorem krylov_selected_ritz_accuracy_of_polynomial {a m l s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + l) (A : Matrix (Fin a) (Fin (m + l)) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (R : Matrix (Fin s) (Fin l) ℝ) (f : Fin r → Fin l) (hf : Function.Injective f)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m))
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    (q : ℝ[X]) (hq : q.natDegree < n)
    {t α L τ : ℝ} (ht : 0 < t) (htα : t ≤ α) (hL : 0 ≤ L) (hτ : 0 ≤ τ)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m))
    (hfilter : ∀ i : Fin m, sp.value (i.castAdd l) < t → |q.eval (sp.value (i.castAdd l))| ≤ τ)
    (hhead : ∀ j : Fin r, 1 ≤ q.eval (sp.value ((f j).natAdd m)))
    {C : ℝ} (hC : 0 ≤ C)
    (hfactor : frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd l) t * U) * R) ≤
      C * (s : ℝ) * frobeniusSq (spectralDeficitMatrix A sp (Fin.castAdd l) t))
    (hbudget : τ ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + l) r hr ⟨0, hr0⟩) := by
  have hα : 0 < α := ht.trans_le htα
  let Rscaled := R * diagonal (fun j : Fin l => (Real.sqrt (sp.value (j.natAdd m)))⁻¹)
  apply krylov_selected_ritz_lower_of_deficit hr0 hr A U sp q hq
    Rscaled f hf (spectral_startingBlock_scaled_rightInverse A sp U R hp hR)
    (fun j => ne_of_gt (by linarith [hhead j])) hh
  have hfiltered := selectedFilteredTailBlock_deficit_bound sp.value (fun i => q.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) Rscaled f (t := t) hτ hfilter hhead
  have htail := spectralDeficit_selected_startingBlock_le A sp U R f hf (t := t) hα hh
  have henergy := spectralDeficitMatrix_frobeniusSq_le_tail A sp (Fin.castAdd l)
    (Fin.castAdd_injective m l) ht.le hl
  have hfac := hfactor.trans (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ C * (s : ℝ)))
  have hinv : α⁻¹ * t ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hα]
    exact htα
  calc
    _ ≤ τ ^ 2 * weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd l)))
        ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd l) id * Rscaled.submatrix id f) := hfiltered
    _ ≤ τ ^ 2 * (α⁻¹ * frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd l) t * U) * R)) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg τ)
    _ ≤ τ ^ 2 * (α⁻¹ * (C * (s : ℝ) * ((m : ℝ) * t * L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac (inv_nonneg.mpr hα.le)) (sq_nonneg τ)
    _ = (α⁻¹ * t) * (τ ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L) := by ring
    _ ≤ 1 * (τ ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L) := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ ≤ α - t := by simpa only [one_mul] using hbudget

end
end LowRank
