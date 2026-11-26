import LowRank.SelectedGapAccuracy
import LowRank.ConfidentKrylovRitz

/-! Gaussian confidence for a selected head Ritz value, with independent
parameters for the spectral gap and the requested additive error. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_gaussian_selected_gap_accuracy_confidence_le {a m l s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + l) (A : Matrix (Fin a) (Fin (m + l)) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin r → Fin l) (hf : Function.Injective f)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m)) (hs : 2 * l + 2 ≤ s)
    {t α L γ η q : ℝ} (ht : 0 < t) (htα : t ≤ α) (hL : 0 < L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m)) (hgap : L * (1 + γ / 2) ≤ α)
    (hbudget : η ^ 2 * (q ^ 2 * (s : ℝ) * (m : ℝ)) * L ≤ α - t) :
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
    exact (not_lt_of_ge (krylov_selected_ritz_gap_accuracy_of_factor hr0 hr A U sp _ f hf hp hU
      ht htα hL hγ hγ1 hη hn hl hh hgap (sq_nonneg q) hfactor hbudget)) hbad
  exact (measure_mono_ae hsub).trans (iidMatrixLaw_startingBlock_confidence_le M V hV hs hq)

theorem krylov_gaussian_gap_ritz_index_confidence_le {a m l s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + l)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m)) (hs : 2 * l + 2 ≤ s)
    (j : Fin l) {L γ η q e : ℝ} (hL : 0 < L) (he : 0 ≤ e)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ η < n)
    (hgap : L * (1 + γ / 2) ≤ sp.value (j.natAdd m))
    (hbudget : η ^ 2 * (q ^ 2 * (s : ℝ) * (m : ℝ)) * L ≤ e) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
          sp.value (j.natAdd m) - e} ≤ ENNReal.ofReal (2 / q) := by
  let t := sp.value (j.natAdd m) - e
  by_cases ht : 0 < t
  · have hr0 : 0 < l - j.val := Nat.sub_pos_of_lt j.isLt
    have hrl : l - j.val ≤ l := Nat.sub_le _ _
    have hr : l - j.val ≤ m + l := by omega
    let f := lastColumnIndex l (l - j.val) hrl
    have hi : lastColumnIndex (m + l) (l - j.val) hr ⟨0, hr0⟩ = j.natAdd m := by
      apply Fin.ext
      change m + l - (l - j.val) + 0 = m + j.val
      omega
    have hh (i : Fin (l - j.val)) : sp.value (j.natAdd m) ≤ sp.value ((f i).natAdd m) := by
      apply sp.increasing
      change m + j.val ≤ m + (l - (l - j.val) + i.val)
      omega
    have h := krylov_gaussian_selected_gap_accuracy_confidence_le hr0 hr A sp f
      (lastColumnIndex_injective l (l - j.val) hrl) hp hs ht (sub_le_self _ he)
      hL hγ hγ1 hη hq hn hl hh hgap (by simpa only [t, sub_sub_cancel] using hbudget)
    simpa only [hi, t] using h
  · have hsub : {U : Matrix (Fin a) (Fin s) ℝ |
        (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
            sp.value (j.natAdd m) - e} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro U hU
      have hnonneg := (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value_nonneg
          (rightGram_posSemidef _) (j.natAdd m)
      exact (not_lt_of_ge (le_trans (le_of_not_gt ht) hnonneg)) hU
    rw [hsub, measure_empty]
    exact zero_le _

end
end LowRank
