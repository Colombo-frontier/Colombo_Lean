import RandomizedFO2003.ContinuousConjugation

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The already proved normalized moments, now expressed using the actual
continuous operators that define the smooth cascade. -/
theorem continuous_rotated_normalized_moments (hγ : 0 < γ) (K : Fin S.size → ℕ)
    (U : BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) (u : BlockSpace K) (hu : ‖u‖ = 1)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - S.weight j| ≤ δ * S.weight j) :
    let a := U (direction K u S.residual)
    let b := U (h • u)
    let Ainv := continuousConjugation U (continuousDiagonal K (fun j => (S.node j)⁻¹))
    let α₀ := h / (64 * γ)
    let D := h ^ 2 / γ
    ‖a‖ = 1 ∧ ‖b‖ = h ∧
      (1 ≤ inner (𝕜 := ℝ) a (Ainv b) / α₀ ∧ inner (𝕜 := ℝ) a (Ainv b) / α₀ ≤ 64) ∧
      (1 ≤ D * inner (𝕜 := ℝ) a (Ainv a) / α₀ ^ 2 ∧
        D * inner (𝕜 := ℝ) a (Ainv a) / α₀ ^ 2 ≤ 4096) ∧
      (0 ≤ inner (𝕜 := ℝ) b (Ainv b) / D ∧ inner (𝕜 := ℝ) b (Ainv b) / D ≤ 1) := by
  have hr := S.rotated_moment_bounds hγ K U u hu h δ hh hδ hδsmall hweight
  have hn := S.normalized_moment_bounds hγ (SpectralCoordinates.weight K u) h δ hh
    (weight_nonneg K u) (unit_weight_sum K u hu) hδ hδsmall hweight
  have hi := S.euclidean_moment_identities K u h
  dsimp only at hr hn hi ⊢
  refine ⟨hr.1, hr.2.1, ?_⟩
  simp only [continuousConjugation_apply_image, U.inner_map_map, continuousDiagonal_apply]
  rw [hi.1, hi.2.1, hi.2.2]
  exact ⟨hn.1, hn.2.1, ⟨(by norm_num : (0 : ℝ) ≤ 1 / 4096).trans hn.2.2.1.1, hn.2.2.1.2⟩⟩

end RandomizedFO2003.FiniteSpectralDesign
