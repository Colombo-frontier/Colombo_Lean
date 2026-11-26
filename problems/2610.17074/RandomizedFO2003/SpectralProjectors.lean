import RandomizedFO2003.SphericalDesign

namespace RandomizedFO2003.SpectralCoordinates

open scoped BigOperators

variable {J : ℕ}

noncomputable def projector (K : Fin J → ℕ) (j : Fin J) : Module.End ℝ (BlockSpace K) :=
  diagonal K (fun i => if i = j then 1 else 0)

theorem projector_idempotent (K : Fin J → ℕ) (j : Fin J) :
    projector K j * projector K j = projector K j := by
  ext x i
  by_cases h : i.1 = j <;> simp [projector, Module.End.mul_apply, h]

theorem projector_orthogonal (K : Fin J → ℕ) (i j : Fin J) (hij : i ≠ j) :
    projector K i * projector K j = 0 := by
  ext x k
  by_cases hi : k.1 = i
  · have hj : k.1 ≠ j := by simpa [hi] using hij
    simp [projector, Module.End.mul_apply, hi, hj, hij]
  · simp [projector, Module.End.mul_apply, hi]

theorem diagonal_self_adjoint (K : Fin J → ℕ) (f : Fin J → ℝ) (x y : BlockSpace K) :
    inner (𝕜 := ℝ) x (diagonal K f y) = inner (𝕜 := ℝ) (diagonal K f x) y := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (f i.1 * y i) * x i = y i * (f i.1 * x i)
  ring

theorem sum_projectors (K : Fin J → ℕ) : ∑ j, projector K j = 1 := by
  ext x i
  simp [LinearMap.sum_apply, block_sum_apply, projector]

theorem projector_eigenvalue (K : Fin J → ℕ) (lam : Fin J → ℝ) (j : Fin J) :
    diagonal K lam * projector K j = lam j • projector K j := by
  ext x i
  by_cases hi : i.1 = j <;> simp [projector, Module.End.mul_apply, hi]

theorem projector_energy (K : Fin J → ℕ) (j : Fin J) (u : BlockSpace K) :
    ‖projector K j u‖ ^ 2 = weight K u j := by
  unfold projector
  rw [norm_diagonal_sq]
  simp [weightedEnergy]

/-- The probability estimates control exactly the physical spectral weights
after any orthogonal rotation and any positive radius scaling. -/
theorem rotated_projector_weight (K : Fin J → ℕ)
    (U : BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) (u : BlockSpace K)
    (j : Fin J) (h : ℝ) (hh : h ≠ 0) :
    ‖conjugation U (projector K j) (U (h • u))‖ ^ 2 / h ^ 2 = weight K u j := by
  rw [conjugation_apply_image, U.norm_map, map_smul, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, projector_energy]
  field_simp

end RandomizedFO2003.SpectralCoordinates
