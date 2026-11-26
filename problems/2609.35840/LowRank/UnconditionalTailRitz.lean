import LowRank.GaussianKrylovExactSupport
import LowRank.SimultaneousTailRitz

/-! Tail-scaled simultaneous Ritz accuracy for every input, including
zero tail eigenvalues and heads containing zero eigenvalues. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_zero_tail_ritz_ae {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hz : ∀ i : Fin m, sp.value (i.castAdd k) = 0) (hs : k ≤ s) (hn : 0 < n) (γ : ℝ) :
    ∀ᵐ U ∂iidMatrixLaw a s 1, U ∈ krylovTailRitzEvent A sp k s n (by omega) γ 0 := by
  filter_upwards [krylov_gaussian_exact_of_zero_tail A sp hz hs hn] with U hU
  intro j
  change sp.value (lastColumnIndex (m + k) k (by omega) j) - (γ / 2) * 0 ≤
    (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + k) k (by omega) j)
  rw [hU]
  simp only [mul_zero, sub_zero,
    (canonicalOrderedSpectrum (m + k) (symmetricRightGram A)).value_unique sp, le_refl]

theorem krylov_zero_tail_ritz_bad_eq_zero {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hz : ∀ i : Fin m, sp.value (i.castAdd k) = 0) (hs : k ≤ s) (hn : 0 < n) (γ : ℝ) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ 0)ᶜ = 0 :=
  ae_iff.mp (krylov_zero_tail_ritz_ae A sp hz hs hn γ)

theorem krylov_simultaneous_tail_ritz_unconditional_confidence_le {a m k s n : ℕ} (hm : 0 < m)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {γ q : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ q s (m + k)) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ
      (sp.value (⟨m - 1, by omega⟩ : Fin (m + k))))ᶜ ≤ ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let iTail : Fin (m + k) := ⟨m - 1, by omega⟩
  have hl (i : Fin m) : sp.value (i.castAdd k) ≤ sp.value iTail := by
    apply sp.increasing
    change i.val ≤ m - 1
    omega
  by_cases hL : sp.value iTail = 0
  · have hz (i : Fin m) : sp.value (i.castAdd k) = 0 :=
      le_antisymm ((hl i).trans_eq hL) (sp.value_nonneg (rightGram_posSemidef A) _)
    change (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ (sp.value iTail))ᶜ ≤ _
    rw [hL, krylov_zero_tail_ritz_bad_eq_zero A sp hz (by omega : k ≤ s)
      ((Nat.zero_le _).trans_lt hn) γ]
    exact zero_le _
  · have hpos : 0 < sp.value iTail := lt_of_le_of_ne
      (sp.value_nonneg (rightGram_posSemidef A) _) (Ne.symm hL)
    apply krylov_simultaneous_tail_ritz_confidence_le A sp _ hs hpos hl hγ hγ1 hq hn
    intro j
    apply hpos.trans_le (sp.increasing _)
    change m - 1 ≤ m + j.val
    omega

theorem krylov_simultaneous_tail_ritz_unconditional_bad_le {a m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ
      (sp.value (⟨m - 1, by omega⟩ : Fin (m + k))))ᶜ ≤ 1 / 20 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have h := krylov_simultaneous_tail_ritz_unconditional_confidence_le hm A sp hs hγ hγ1
    (by positivity : 0 < 40 * (k : ℝ)) hn
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
  exact h

theorem krylov_simultaneous_tail_ritz_unconditional_success {a m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n) :
    19 / 20 ≤ (iidMatrixLaw a s 1).real (krylovTailRitzEvent A sp k s n (by omega) γ
      (sp.value (⟨m - 1, by omega⟩ : Fin (m + k)))) := by
  have hbad := krylov_simultaneous_tail_ritz_unconditional_bad_le hm hk0 A sp hs hγ hγ1 hn
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw a s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_krylovTailRitzEvent A sp k s n (by omega) γ _),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

end
end LowRank
