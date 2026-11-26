import LowRank.TailScaledKrylovRitz

/-! Separate the spectral gap from the requested additive Ritz error.
A fixed gap permits arbitrarily small errors by reducing the tolerance. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem krylov_selected_ritz_gap_accuracy_of_factor {a m l s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + l) (A : Matrix (Fin a) (Fin (m + l)) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (R : Matrix (Fin s) (Fin l) ℝ) (f : Fin r → Fin l) (hf : Function.Injective f)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m))
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    {t α L γ η : ℝ} (ht : 0 < t) (htα : t ≤ α) (hL : 0 < L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m))
    (hgap : L * (1 + γ / 2) ≤ α) {C : ℝ} (hC : 0 ≤ C)
    (hfactor : frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd l) t * U) * R) ≤
      C * (s : ℝ) * frobeniusSq (spectralDeficitMatrix A sp (Fin.castAdd l) t))
    (hbudget : η ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + l) r hr ⟨0, hr0⟩) := by
  have hα : 0 < α := ht.trans_le htα
  let q := chebyshevGapFilter L γ (chebyshevFilterDegree γ η)
  have hspec := chebyshevGapFilter_spec hL hγ hγ1 hη
  have hhead (j : Fin r) : 1 ≤ q.eval (sp.value ((f j).natAdd m)) :=
    hspec.2.2 _ (hgap.trans (hh j))
  let Rscaled := R * diagonal (fun j : Fin l => (Real.sqrt (sp.value (j.natAdd m)))⁻¹)
  apply krylov_selected_ritz_lower_of_deficit hr0 hr A U sp q (hspec.1.trans_lt hn)
    Rscaled f hf (spectral_startingBlock_scaled_rightInverse A sp U R hp hR)
    (fun j => ne_of_gt (by linarith [hhead j])) hh
  have hfilter := selectedFilteredTailBlock_deficit_bound sp.value (fun i => q.eval (sp.value i))
    (sp.basisᵀ * (Aᵀ * U)) Rscaled f (t := t) hη.le
    (fun i _ => hspec.2.1 _ (sp.value_nonneg (rightGram_posSemidef A) _) (hl i)) hhead
  have htail := spectralDeficit_selected_startingBlock_le A sp U R f hf (t := t) hα hh
  have henergy := spectralDeficitMatrix_frobeniusSq_le_tail A sp (Fin.castAdd l)
    (Fin.castAdd_injective m l) ht.le hl
  have hfac := hfactor.trans (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ C * (s : ℝ)))
  have hinv : α⁻¹ * t ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hα]
    exact htα
  calc
    _ ≤ η ^ 2 * weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd l)))
        ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd l) id * Rscaled.submatrix id f) := hfilter
    _ ≤ η ^ 2 * (α⁻¹ * frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd l) t * U) * R)) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg η)
    _ ≤ η ^ 2 * (α⁻¹ * (C * (s : ℝ) * ((m : ℝ) * t * L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac (inv_nonneg.mpr hα.le)) (sq_nonneg η)
    _ = (α⁻¹ * t) * (η ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L) := by ring
    _ ≤ 1 * (η ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L) :=
      mul_le_mul_of_nonneg_right hinv (by positivity)
    _ ≤ α - t := by simpa only [one_mul] using hbudget

end
end LowRank
