import LowRank.TailScaledKrylovRitz
import LowRank.ConfidentKrylovRitz

/-! Adjustable Gaussian confidence for additive Ritz errors on the scale
of the fixed tail spectrum. Positivity is explicit in this module. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_gaussian_selected_ritz_tail_confidence_le {a m k s r n : ℕ}
    (hr0 : 0 < r) (hr : r ≤ m + k) (A : Matrix (Fin a) (Fin (m + k)) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin r → Fin k) (hf : Function.Injective f)
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (hs : 2 * k + 2 ≤ s)
    {t L γ η q : ℝ} (ht : 0 < t) (hL : 0 < L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ η < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L)
    (hh : ∀ j : Fin r, t + (γ / 2) * L ≤ sp.value ((f j).natAdd m))
    (hbudget : η ^ 2 * (q ^ 2 * (s : ℝ) * (m : ℝ)) ≤ γ / 2) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
          (lastColumnIndex (m + k) r hr ⟨0, hr0⟩) < t} ≤ ENNReal.ofReal (2 / q) := by
  let V := positiveSpectralLeftColumns A sp (Fin.natAdd m)
  let M := spectralDeficitMatrix A sp (Fin.castAdd k) t
  have hV : Vᵀ * V = 1 :=
    positiveSpectralLeftColumns_orthogonal A sp (Fin.natAdd m) (Fin.natAddEmb m).injective hp
  have hsub : ∀ᵐ U ∂iidMatrixLaw a s 1,
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
          (lastColumnIndex (m + k) r hr ⟨0, hr0⟩) < t) →
        q ^ 2 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U)) := by
    filter_upwards [iidMatrixLaw_compressed_rightInverse_ae V hV (by omega : k ≤ s)
      (by norm_num : (1 : NNReal) ≠ 0)] with U hU
    intro hbad
    by_contra! hfactor
    exact (not_lt_of_ge (krylov_selected_ritz_tail_scaled_of_factor hr0 hr A U sp _ f hf hp hU
      ht hL hγ hγ1 hη hn hl hh (sq_nonneg q) hfactor hbudget)) hbad
  exact (measure_mono_ae hsub).trans (iidMatrixLaw_startingBlock_confidence_le M V hV hs hq)

theorem krylov_gaussian_tail_ritz_index_confidence_le {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (hs : 2 * k + 2 ≤ s)
    (j : Fin k) {L γ q : ℝ} (hL : 0 < L)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ q s (m + k)) < n) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
          sp.value (j.natAdd m) - (γ / 2) * L} ≤ ENNReal.ofReal (2 / q) := by
  let t := sp.value (j.natAdd m) - (γ / 2) * L
  by_cases ht : 0 < t
  · have hr0 : 0 < k - j.val := Nat.sub_pos_of_lt j.isLt
    have hrk : k - j.val ≤ k := Nat.sub_le _ _
    have hr : k - j.val ≤ m + k := by omega
    let f := lastColumnIndex k (k - j.val) hrk
    have he : lastColumnIndex (m + k) (k - j.val) hr ⟨0, hr0⟩ = j.natAdd m := by
      apply Fin.ext
      change m + k - (k - j.val) + 0 = m + j.val
      omega
    have hh (i : Fin (k - j.val)) : t + (γ / 2) * L ≤ sp.value ((f i).natAdd m) := by
      dsimp only [t]
      rw [sub_add_cancel]
      apply sp.increasing
      change m + j.val ≤ m + (k - (k - j.val) + i.val)
      omega
    have h := krylov_gaussian_selected_ritz_tail_confidence_le hr0 hr A sp f
      (lastColumnIndex_injective k (k - j.val) hrk) hp hs ht hL hγ hγ1
      (confidentRitzTolerance_pos hγ hq (by omega : 0 < s)) hq hn hl hh
      (confidentRitzTolerance_budget hγ.le hq (by omega : 0 < s) (by omega : m ≤ m + k))
    simpa only [he, t] using h
  · have he : {U : Matrix (Fin a) (Fin s) ℝ |
        (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
            sp.value (j.natAdd m) - (γ / 2) * L} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro U hU
      have hnonneg := (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value_nonneg
          (rightGram_posSemidef _) (j.natAdd m)
      exact (not_lt_of_ge (le_trans (le_of_not_gt ht) hnonneg)) hU
    rw [he, measure_empty]
    exact zero_le _

end
end LowRank
