import RandomizedFO2003.MultiplicityBlock

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The three scalar formulas are exactly the moments of the full Euclidean
block, with arbitrary multiplicities, rather than an assumed moment model. -/
theorem euclidean_moment_identities (K : Fin D.size → ℕ) (u : BlockSpace K) (h : ℝ) :
    let a := direction K u D.residual
    let b := h • u
    let Ainv := diagonal K (fun j => (D.node j)⁻¹)
    inner (𝕜 := ℝ) a (Ainv b) = D.alpha (SpectralCoordinates.weight K u) h ∧
      inner (𝕜 := ℝ) a (Ainv a) = D.beta (SpectralCoordinates.weight K u) ∧
      inner (𝕜 := ℝ) b (Ainv b) = D.rho (SpectralCoordinates.weight K u) h := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [map_smul, direction_inner]
    rfl
  · exact direction_inverse_inner K u D.residual (fun j => (D.node j)⁻¹)
  · exact scaled_inverse_inner K u (fun j => (D.node j)⁻¹) h

theorem euclidean_moment_bounds (hγ : 0 < γ) (K : Fin D.size → ℕ)
    (u : BlockSpace K) (hu : ‖u‖ = 1) (h δ : ℝ) (hh : 0 < h)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j) :
    let a := direction K u D.residual
    let b := h • u
    let Ainv := diagonal K (fun j => (D.node j)⁻¹)
    ‖a‖ = 1 ∧ ‖b‖ = h ∧
      (h / (64 * γ) ≤ inner (𝕜 := ℝ) a (Ainv b) ∧
        inner (𝕜 := ℝ) a (Ainv b) ≤ h / γ) ∧
      (1 / (4096 * γ) ≤ inner (𝕜 := ℝ) a (Ainv a) ∧
        inner (𝕜 := ℝ) a (Ainv a) ≤ 1 / γ) ∧
      (h ^ 2 / (4096 * γ) ≤ inner (𝕜 := ℝ) b (Ainv b) ∧
        inner (𝕜 := ℝ) b (Ainv b) ≤ h ^ 2 / γ) := by
  dsimp only
  have hR := D.empirical_residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
    (SpectralCoordinates.weight K u) δ (by linarith) hweight
  obtain ⟨ha, hb, hr⟩ := D.euclidean_moment_identities K u h
  dsimp only at ha hb hr
  rw [ha, hb, hr]
  obtain ⟨hblo, hrlo⟩ := D.moment_lower_bounds hγ (SpectralCoordinates.weight K u) h δ hh
    (weight_nonneg K u) (unit_weight_sum K u hu) hδ hδsmall hweight
  refine ⟨direction_norm K u D.residual hR, ?_,
    ⟨D.alpha_lower hγ _ _ _ hh hδ hδsmall hweight,
      D.alpha_upper hγ _ _ hh.le (weight_nonneg K u) (unit_weight_sum K u hu) hR⟩,
    ⟨hblo, ?_⟩, ⟨hrlo, D.rho_upper hγ _ _ (weight_nonneg K u) (unit_weight_sum K u hu)⟩⟩
  · simp [norm_smul, Real.norm_eq_abs, abs_of_pos hh, hu]
  · simpa [one_div] using D.beta_upper hγ (SpectralCoordinates.weight K u) (weight_nonneg K u) hR

/-- The short-Krylov readout estimate for genuine polynomial evaluation of
the full Euclidean operator. The statement also covers p(A)b=0. -/
theorem euclidean_short_krylov_bound (hγ : 0 < γ) (K : Fin D.size → ℕ)
    (u : BlockSpace K) (h δ : ℝ) (hh : 0 ≤ h)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j)
    (p : Polynomial ℝ) (hp : p.natDegree < m) :
    let a := direction K u D.residual
    let b := h • u
    let A := diagonal K D.node
    let pb := (p.eval₂ (algebraMap ℝ (Module.End ℝ (BlockSpace K))) A) b
    |inner (𝕜 := ℝ) a pb| ≤ 2 * δ * ‖pb‖ := by
  dsimp only
  rw [polynomial_diagonal, map_smul, direction_inner, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hh, norm_diagonal]
  have hR := D.empirical_residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
    (SpectralCoordinates.weight K u) δ (by linarith) hweight
  have hs := D.short_polynomial_pairing_bound (SpectralCoordinates.weight K u) δ (weight_nonneg K u)
    hδ hδhalf hweight p hp
  rw [abs_div, abs_mul, abs_of_nonneg hh, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  have hhbound := mul_le_mul_of_nonneg_left hs hh
  nlinarith

end RandomizedFO2003.FiniteSpectralDesign

