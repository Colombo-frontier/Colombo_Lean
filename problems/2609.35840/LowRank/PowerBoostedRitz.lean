import LowRank.PowerBoostedFilter
import LowRank.SelectedPolynomialAccuracy
import LowRank.GapAccuracyConfidence

/-! A power-boosted filter supplies selected Ritz accuracy with error
decaying as a power of the tail-to-head ratio. -/

namespace LowRank
open Matrix MeasureTheory Polynomial
open scoped Matrix ENNReal
noncomputable section

theorem krylov_selected_power_boosted_ritz_of_factor {a m l s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + l) (A : Matrix (Fin a) (Fin (m + l)) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (R : Matrix (Fin s) (Fin l) ℝ) (f : Fin r → Fin l) (hf : Function.Injective f)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m))
    (hR : ((positiveSpectralLeftColumns A sp (Fin.natAdd m))ᵀ * U) * R = 1)
    (u : ℕ) {t α c L γ η : ℝ} (ht : 0 < t) (htα : t ≤ α)
    (hc : 0 < c) (hcL : c ≤ L) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η)
    (hn : chebyshevFilterDegree γ η + u < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hlc : ∀ i : Fin m, sp.value (i.castAdd l) < t → sp.value (i.castAdd l) ≤ c)
    (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m)) (hgap : c * (1 + γ / 2) ≤ α)
    {C : ℝ} (hC : 0 ≤ C)
    (hfactor : frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd l) t * U) * R) ≤
      C * (s : ℝ) * frobeniusSq (spectralDeficitMatrix A sp (Fin.castAdd l) t))
    (hbudget : (η * (L / α) ^ u) ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L ≤ α - t) :
    t ≤ (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + l) r hr ⟨0, hr0⟩) := by
  have hα : 0 < α := ht.trans_le htα
  have hL : 0 ≤ L := hc.le.trans hcL
  let q := powerBoostedFilter (chebyshevGapFilter c γ (chebyshevFilterDegree γ η)) α u
  have hspec := powerBoostedChebyshev_spec u hc hα hγ hγ1 hη hgap
  refine krylov_selected_ritz_accuracy_of_polynomial hr0 hr A U sp R f hf hp hR q
    (hspec.1.trans_lt hn) ht htα hL (by positivity) hl hh ?_ ?_ hC hfactor hbudget
  · intro i hi
    exact (hspec.2.1 _ (sp.value_nonneg (rightGram_posSemidef A) _) (hlc i hi)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hc.le hα.le) (div_le_div_of_nonneg_right hcL hα.le) u) hη.le)
  · intro j
    exact hspec.2.2 _ (hh j)

theorem krylov_gaussian_selected_power_boosted_confidence_le {a m l s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + l) (A : Matrix (Fin a) (Fin (m + l)) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin r → Fin l) (hf : Function.Injective f)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m)) (hs : 2 * l + 2 ≤ s)
    (u : ℕ) {t α c L γ η q : ℝ} (ht : 0 < t) (htα : t ≤ α)
    (hc : 0 < c) (hcL : c ≤ L) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ η + u < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hlc : ∀ i : Fin m, sp.value (i.castAdd l) < t → sp.value (i.castAdd l) ≤ c)
    (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m)) (hgap : c * (1 + γ / 2) ≤ α)
    (hbudget : (η * (L / α) ^ u) ^ 2 * (q ^ 2 * (s : ℝ) * (m : ℝ)) * L ≤ α - t) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
          (lastColumnIndex (m + l) r hr ⟨0, hr0⟩) < t} ≤ ENNReal.ofReal (2 / q) := by
  let V := positiveSpectralLeftColumns A sp (Fin.natAdd m)
  let M := spectralDeficitMatrix A sp (Fin.castAdd l) t
  have hV : Vᵀ * V = 1 :=
    positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  have hsub : ∀ᵐ U ∂iidMatrixLaw a s 1,
      ((canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
          (lastColumnIndex (m + l) r hr ⟨0, hr0⟩) < t) →
        q ^ 2 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U)) := by
    filter_upwards [iidMatrixLaw_compressed_rightInverse_ae V hV (by omega : l ≤ s)
      (by norm_num : (1 : NNReal) ≠ 0)] with U hU
    intro hbad
    by_contra! hfactor
    exact (not_lt_of_ge (krylov_selected_power_boosted_ritz_of_factor hr0 hr A U sp _ f hf hp hU
      u ht htα hc hcL hγ hγ1 hη hn hl hlc hh hgap (sq_nonneg q) hfactor hbudget)) hbad
  exact (measure_mono_ae hsub).trans (iidMatrixLaw_startingBlock_confidence_le M V hV hs hq)

end
end LowRank
