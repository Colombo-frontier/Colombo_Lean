import RandomizedFO2003.ExposureFrame

namespace RandomizedFO2003.Rotations

variable {S E : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An isometric embedding's adjoint recovers its input. -/
@[simp] theorem embedding_adjoint_self (L : S →ₗᵢ[ℝ] E) (x : S) :
    L.toContinuousLinearMap.adjoint (L x) = x := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact L.inner_map_map y x

/-- Extend a rotation of embedded coordinates to an ambient orthogonal map. -/
noncomputable def extendEmbedding (L : S →ₗᵢ[ℝ] E) (R : S ≃ₗᵢ[ℝ] S) : E ≃ₗᵢ[ℝ] E :=
  let J := L.comp (R.toLinearIsometry.comp L.equivRange.symm.toLinearIsometry)
  LinearIsometryEquiv.ofSurjective J.extend
    (LinearMap.surjective_of_injective (f := J.extend.toLinearMap) J.extend.injective)

omit [FiniteDimensional ℝ S] in
@[simp] theorem extendEmbedding_apply (L : S →ₗᵢ[ℝ] E) (R : S ≃ₗᵢ[ℝ] S) (x : S) :
    extendEmbedding L R (L x) = L (R x) := by
  let J := L.comp (R.toLinearIsometry.comp L.equivRange.symm.toLinearIsometry)
  change J.extend (L x) = L (R x)
  have h := LinearIsometry.extend_apply J (L.equivRange x)
  simpa [J] using h

/-- The ambient extension intertwines the adjoint projection and rotation. -/
theorem adjoint_extendEmbedding (L : S →ₗᵢ[ℝ] E) (R : S ≃ₗᵢ[ℝ] S) (x : E) :
    L.toContinuousLinearMap.adjoint (extendEmbedding L R x) = R (L.toContinuousLinearMap.adjoint x) := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    inner (𝕜 := ℝ) (L y) (extendEmbedding L R x) =
        inner (𝕜 := ℝ) (extendEmbedding L R (L (R.symm y))) (extendEmbedding L R x) := by simp
    _ = inner (𝕜 := ℝ) (L (R.symm y)) x := (extendEmbedding L R).inner_map_map _ _
    _ = inner (𝕜 := ℝ) (R.symm y) (L.toContinuousLinearMap.adjoint x) :=
      (ContinuousLinearMap.adjoint_inner_right L.toContinuousLinearMap (R.symm y) x).symm
    _ = inner (𝕜 := ℝ) y (R (L.toContinuousLinearMap.adjoint x)) := by
      rw [← R.inner_map_map (R.symm y) (L.toContinuousLinearMap.adjoint x),
        LinearIsometryEquiv.apply_symm_apply]

end RandomizedFO2003.Rotations
