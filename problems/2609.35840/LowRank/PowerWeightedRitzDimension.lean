import LowRank.WidePowerWeightedRitz

/-! Ambient-dimension interfaces for both weighted Ritz branches. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_power_weighted_bad_le_dim {a d k s n : ℕ}
    (hk : k < d) (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin d) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) (u : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : chebyshevFilterDegree (powerBoostedGap δ u)
      (confidentRitzTolerance δ (40 * (k : ℝ)) s d) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u hk.le δ
      (sp.value (⟨d - k - 1, by omega⟩ : Fin d)))ᶜ ≤ 1 / 20 := by
  obtain ⟨m, hm, hd⟩ : ∃ m : ℕ, 0 < m ∧ d = m + k := ⟨d - k, by omega, by omega⟩
  subst d
  simpa only [Nat.add_sub_cancel] using
    krylov_power_weighted_ritz_unconditional_bad_le hm hk0 A sp hs u hδ hδ1 hn

theorem krylov_wide_power_weighted_bad_le_dim {a d l k s n : ℕ}
    (hl : l < d) (hk0 : 0 < k) (hkl : k ≤ l)
    (A : Matrix (Fin a) (Fin d) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * l + 2 ≤ s) (u : ℕ) {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hgap : sp.value (⟨d - l - 1, by omega⟩ : Fin d) ≤ T / 2)
    (hhead : ∀ j : Fin k, T ≤ sp.value (lastColumnIndex d k (by omega) j))
    (hn : chebyshevFilterDegree 1 (confidentRitzTolerance δ (40 * (k : ℝ)) s d) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ T)ᶜ ≤ 1 / 20 := by
  obtain ⟨m, hm, hd⟩ : ∃ m : ℕ, 0 < m ∧ d = m + l := ⟨d - l, by omega, by omega⟩
  subst d
  have hgap' : sp.value (⟨m - 1, by omega⟩ : Fin (m + l)) ≤ T / 2 := by
    simpa only [Nat.add_sub_cancel] using hgap
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have h := krylov_wide_power_weighted_unconditional_confidence_le hm A sp hkl hs u hT hδ
    (by positivity : 0 < 40 * (k : ℝ)) hgap' hhead hn
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
  exact h

end
end LowRank
