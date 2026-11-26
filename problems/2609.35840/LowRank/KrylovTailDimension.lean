import LowRank.WideGapRitz

/-! Dimension-independent interfaces for the narrow and wide Ritz events. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_tail_ritz_bad_le_dim {a d k s n : ℕ}
    (hk : k < d) (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin d) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s d) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n hk.le γ
      (sp.value (⟨d - k - 1, by omega⟩ : Fin d)))ᶜ ≤ 1 / 20 := by
  obtain ⟨m, hm, hd⟩ : ∃ m : ℕ, 0 < m ∧ d = m + k := ⟨d - k, by omega, by omega⟩
  subst d
  simpa only [Nat.add_sub_cancel] using
    krylov_simultaneous_tail_ritz_unconditional_bad_le hm hk0 A sp hs hγ hγ1 hn

theorem krylov_wide_tail_gap_bad_le_dim {a d l k s n : ℕ}
    (hl : l < d) (hk0 : 0 < k) (hkl : k ≤ l)
    (A : Matrix (Fin a) (Fin d) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * l + 2 ≤ s) {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ)
    (hgap : sp.value (⟨d - l - 1, by omega⟩ : Fin d) ≤ T / 2)
    (hhead : ∀ j : Fin k, T ≤ sp.value (lastColumnIndex d k (by omega) j))
    (hn : chebyshevFilterDegree 1 (confidentRitzTolerance γ (40 * (k : ℝ)) s d) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ T)ᶜ ≤ 1 / 20 := by
  obtain ⟨m, hm, hd⟩ : ∃ m : ℕ, 0 < m ∧ d = m + l := ⟨d - l, by omega, by omega⟩
  subst d
  have hgap' : sp.value (⟨m - 1, by omega⟩ : Fin (m + l)) ≤ T / 2 := by
    simpa only [Nat.add_sub_cancel] using hgap
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have heγ : 2 * (γ / 2) = γ := by ring
  have h := krylov_wide_tail_gap_confidence_le hm A sp hkl hs hT
    (by positivity : 0 < γ / 2) (by positivity : 0 < 40 * (k : ℝ)) hgap' hhead
    (by simpa only [heγ] using hn)
  rw [heγ] at h
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
  exact h

end
end LowRank
