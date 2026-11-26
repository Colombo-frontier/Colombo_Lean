import RandomizedFO2003.SpectralOperatorBounds

namespace RandomizedFO2003.SpectralCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def continuousConjugation (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem continuousConjugation_apply (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) (x : E) :
    continuousConjugation U A x = U (A (U.symm x)) := rfl

theorem continuousConjugation_toLinearMap (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) :
    (continuousConjugation U A).toLinearMap = conjugation U A.toLinearMap := by ext x; rfl

@[simp] theorem continuousConjugation_apply_image (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) (x : E) :
    continuousConjugation U A (U x) = U (A x) := by simp

theorem continuousConjugation_norm_le (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) :
    ‖continuousConjugation U A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  simpa using A.le_opNorm (U.symm x)

theorem continuousConjugation_coercive (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) (γ : ℝ)
    (hA : ∀ x, γ * ‖x‖ ≤ ‖A x‖) (x : E) : γ * ‖x‖ ≤ ‖continuousConjugation U A x‖ := by
  simpa using hA (U.symm x)

theorem continuousConjugation_nonneg (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E)
    (hA : ∀ x, 0 ≤ inner (𝕜 := ℝ) x (A x)) (x : E) :
    0 ≤ inner (𝕜 := ℝ) x (continuousConjugation U A x) := by
  obtain ⟨y, rfl⟩ := U.surjective x
  simpa only [continuousConjugation_apply_image, U.inner_map_map] using hA y

theorem continuousConjugation_inverse_left (U : E ≃ₗᵢ[ℝ] E) (A L : E →L[ℝ] E)
    (hLA : ∀ x, L (A x) = x) (x : E) :
    continuousConjugation U L (continuousConjugation U A x) = x := by
  simp only [continuousConjugation_apply, U.symm_apply_apply, hLA, U.apply_symm_apply]

variable [CompleteSpace E]

theorem continuousConjugation_selfAdjoint (U : E ≃ₗᵢ[ℝ] E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (continuousConjugation U A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  obtain ⟨x, rfl⟩ := U.surjective x
  obtain ⟨y, rfl⟩ := U.surjective y
  change inner (𝕜 := ℝ) (continuousConjugation U A (U x)) (U y) =
    inner (𝕜 := ℝ) (U x) (continuousConjugation U A (U y))
  simpa only [continuousConjugation_apply_image, U.inner_map_map] using hA.isSymmetric x y

end RandomizedFO2003.SpectralCoordinates
