import LowRank.SelectedDeficitEnergy

/-! A fixed tail cutoff controls the additive error of any selected Ritz
value, even when the remaining head eigenvalues are much larger. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem min_cutoff_gap {t L γ : ℝ} (hγ : 0 ≤ γ) :
    min t L * (1 + γ / 2) ≤ t + (γ / 2) * L := by
  have h := mul_le_mul_of_nonneg_left (min_le_right t L) (by linarith : 0 ≤ γ / 2)
  have ht := min_le_left t L
  nlinarith

theorem spectral_startingBlock_scaled_rightInverse {a m k s : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (U : Matrix (Fin a) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m))
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1) :
    (sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.natAdd m) id *
      (R * diagonal (fun j : Fin k => (Real.sqrt (sp.value (j.natAdd m)))⁻¹)) =
        (1 : Matrix (Fin k) (Fin k) ℝ) := by
  let c := fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))
  have hc (j : Fin k) : c j ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp j))
  have hinv : diagonal c * diagonal (fun j => (c j)⁻¹) = 1 := diagonal_mul_reciprocal c hc
  rw [spectral_startingBlock_factor A sp (Fin.natAdd m) hp U]
  change (diagonal c * ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U)) *
    (R * diagonal (fun j => (c j)⁻¹)) = 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U),
    hR, Matrix.one_mul, hinv]

theorem krylov_selected_ritz_tail_scaled_of_factor {a m k s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + k) (A : Matrix (Fin a) (Fin (m + k)) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (R : Matrix (Fin s) (Fin k) ℝ) (f : Fin r → Fin k) (hf : Function.Injective f)
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m))
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    {t L γ η : ℝ} (ht : 0 < t) (hL : 0 < L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L)
    (hh : ∀ j : Fin r, t + (γ / 2) * L ≤ sp.value ((f j).natAdd m))
    {C : ℝ} (hC : 0 ≤ C)
    (hfactor : frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R) ≤
      C * (s : ℝ) * frobeniusSq (spectralDeficitMatrix A sp (Fin.castAdd k) t))
    (hbudget : η ^ 2 * (C * (s : ℝ) * (m : ℝ)) ≤ γ / 2) :
    t ≤ (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + k) r hr ⟨0, hr0⟩) := by
  let α := t + (γ / 2) * L
  have htα : t ≤ α := le_add_of_nonneg_right (by positivity)
  have hα : 0 < α := ht.trans_le htα
  let q := chebyshevGapFilter (min t L) γ (chebyshevFilterDegree γ η)
  have hspec := chebyshevGapFilter_spec (lt_min ht hL) hγ hγ1 hη
  have hhead (j : Fin r) : 1 ≤ q.eval (sp.value ((f j).natAdd m)) :=
    hspec.2.2 _ ((min_cutoff_gap hγ.le).trans (hh j))
  let Rscaled := R * diagonal (fun j : Fin k => (Real.sqrt (sp.value (j.natAdd m)))⁻¹)
  apply krylov_selected_ritz_lower_of_deficit hr0 hr A U sp q (hspec.1.trans_lt hn)
    Rscaled f hf (spectral_startingBlock_scaled_rightInverse A sp U R hp hR)
    (fun j => ne_of_gt (by linarith [hhead j])) hh
  have hfilter := selectedFilteredTailBlock_deficit_bound sp.value (fun i => q.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) Rscaled f hη.le
    (fun i hi => hspec.2.1 _ (sp.value_nonneg (rightGram_posSemidef A) _)
      (le_min hi.le (hl i))) hhead
  have htail := spectralDeficit_selected_startingBlock_le A sp U R f hf (t := t) hα hh
  have henergy := spectralDeficitMatrix_frobeniusSq_le_tail A sp (Fin.castAdd k)
    (Fin.castAdd_injective m k) ht.le hl
  have hfac := hfactor.trans (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ C * (s : ℝ)))
  have hinv : α⁻¹ * t ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hα]
    exact htα
  have hprod : 0 ≤ η ^ 2 * (C * (s : ℝ) * (m : ℝ)) := by positivity
  calc
    _ ≤ η ^ 2 * weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
        ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id * Rscaled.submatrix id f) := hfilter
    _ ≤ η ^ 2 * (α⁻¹ * frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R)) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg η)
    _ ≤ η ^ 2 * (α⁻¹ * (C * (s : ℝ) * ((m : ℝ) * t * L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac (inv_nonneg.mpr hα.le)) (sq_nonneg η)
    _ = (α⁻¹ * t) * (η ^ 2 * (C * (s : ℝ) * (m : ℝ))) * L := by ring
    _ ≤ (1 * (γ / 2)) * L := mul_le_mul_of_nonneg_right
      (mul_le_mul hinv hbudget hprod (by norm_num)) hL.le
    _ = (t + (γ / 2) * L) - t := by ring

end
end LowRank
