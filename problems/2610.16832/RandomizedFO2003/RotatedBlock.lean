import RandomizedFO2003.EuclideanBlock
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace RandomizedFO2003.SpectralCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal conjugation, as an algebra equivalence on genuine operators. -/
noncomputable def conjugation (U : E ≃ₗᵢ[ℝ] E) : Module.End ℝ E ≃ₐ[ℝ] Module.End ℝ E :=
  { U.toLinearEquiv.conjRingEquiv with
    commutes' := by
      intro c
      ext x
      change U (c • U.symm x) = c • x
      rw [map_smul, U.apply_symm_apply] }

theorem conjugation_apply (U : E ≃ₗᵢ[ℝ] E) (T : Module.End ℝ E) (x : E) :
    conjugation U T x = U (T (U.symm x)) := rfl

theorem conjugation_apply_image (U : E ≃ₗᵢ[ℝ] E) (T : Module.End ℝ E) (x : E) :
    conjugation U T (U x) = U (T x) := by rw [conjugation_apply, U.symm_apply_apply]

theorem polynomial_conjugation (U : E ≃ₗᵢ[ℝ] E) (T : Module.End ℝ E) (p : Polynomial ℝ) :
    p.eval₂ (algebraMap ℝ (Module.End ℝ E)) (conjugation U T) =
      conjugation U (p.eval₂ (algebraMap ℝ (Module.End ℝ E)) T) :=
  Polynomial.aeval_algHom_apply (conjugation U) T p

theorem inner_conjugation (U : E ≃ₗᵢ[ℝ] E) (T : Module.End ℝ E) (x y : E) :
    inner (𝕜 := ℝ) (U x) (conjugation U T (U y)) = inner (𝕜 := ℝ) x (T y) := by
  rw [conjugation_apply_image, U.inner_map_map]

theorem inverse_conjugation (U : E ≃ₗᵢ[ℝ] E) (T S : Module.End ℝ E)
    (hTS : T * S = 1) (hST : S * T = 1) :
    conjugation U T * conjugation U S = 1 ∧
      conjugation U S * conjugation U T = 1 := by
  constructor
  · rw [← map_mul, hTS, map_one]
  · rw [← map_mul, hST, map_one]

end RandomizedFO2003.SpectralCoordinates

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

theorem rotated_moment_bounds (hγ : 0 < γ) (K : Fin D.size → ℕ)
    (U : BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) (u : BlockSpace K) (hu : ‖u‖ = 1)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j) :
    let a := U (direction K u D.residual)
    let b := U (h • u)
    let Ainv := conjugation U (diagonal K (fun j => (D.node j)⁻¹))
    ‖a‖ = 1 ∧ ‖b‖ = h ∧
      (h / (64 * γ) ≤ inner (𝕜 := ℝ) a (Ainv b) ∧
        inner (𝕜 := ℝ) a (Ainv b) ≤ h / γ) ∧
      (1 / (4096 * γ) ≤ inner (𝕜 := ℝ) a (Ainv a) ∧
        inner (𝕜 := ℝ) a (Ainv a) ≤ 1 / γ) ∧
      (h ^ 2 / (4096 * γ) ≤ inner (𝕜 := ℝ) b (Ainv b) ∧
        inner (𝕜 := ℝ) b (Ainv b) ≤ h ^ 2 / γ) := by
  dsimp only
  simp only [inner_conjugation, U.norm_map]
  exact D.euclidean_moment_bounds hγ K u hu h δ hh hδ hδsmall hweight

theorem rotated_short_krylov_bound (hγ : 0 < γ) (K : Fin D.size → ℕ)
    (U : BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) (u : BlockSpace K)
    (h δ : ℝ) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j)
    (p : Polynomial ℝ) (hp : p.natDegree < m) :
    let a := U (direction K u D.residual)
    let b := U (h • u)
    let A := conjugation U (diagonal K D.node)
    let pb := (p.eval₂ (algebraMap ℝ (Module.End ℝ (BlockSpace K))) A) b
    |inner (𝕜 := ℝ) a pb| ≤ 2 * δ * ‖pb‖ := by
  dsimp only
  rw [polynomial_conjugation, conjugation_apply_image, U.inner_map_map, U.norm_map]
  exact D.euclidean_short_krylov_bound hγ K u h δ hh hδ hδhalf hweight p hp

end RandomizedFO2003.FiniteSpectralDesign
