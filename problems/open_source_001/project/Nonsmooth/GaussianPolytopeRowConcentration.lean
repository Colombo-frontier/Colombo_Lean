import Nonsmooth.AffineGaussianPolytopeConcentration

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeRow_centered_mgf (s : ℝ) (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : GaussianPolytopeRow s ν) (q : E) (t : ℝ) :
    Integrable (fun z : E => Real.exp (t * (⟪q, z⟫_ℝ - ∫ y, ⟪q, y⟫_ℝ ∂ν))) ν ∧
      (∫ z : E, Real.exp (t * (⟪q, z⟫_ℝ - ∫ y, ⟪q, y⟫_ℝ ∂ν)) ∂ν) ≤
        Real.exp (t ^ 2 * s ^ 2 * ‖q‖ ^ 2 / 2) := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · constructor
    · exact integrable_dirac (by simp)
    · simp only [integral_dirac, sub_self, mul_zero, Real.exp_zero]
      exact Real.one_le_exp_iff.mpr (by positivity)
  · exact gaussianPolytopeModel_centered_mgf s M q t

theorem gaussianPolytopeRow_vector_centered_mgf (s : ℝ) (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : GaussianPolytopeRow s ν) (v : E) :
    Integrable (fun z : E => Real.exp ⟪v, z - ∫ y : E, y ∂ν⟫_ℝ) ν ∧
      (∫ z : E, Real.exp ⟪v, z - ∫ y : E, y ∂ν⟫_ℝ ∂ν) ≤
        Real.exp (s ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hi := (gaussianPolytopeRow_memLp s ν hν).integrable (by norm_num)
  simpa only [one_pow, one_mul, integral_inner hi, inner_sub_right] using
    gaussianPolytopeRow_centered_mgf s ν hν v 1

theorem gaussianPolytopeRow_dimension_centered_mgf (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : GaussianPolytopeRow ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) ν) (v : E) :
    Integrable (fun z : E => Real.exp ⟪v, z - ∫ y : E, y ∂ν⟫_ℝ) ν ∧
      (∫ z : E, Real.exp ⟪v, z - ∫ y : E, y ∂ν⟫_ℝ ∂ν) ≤
        Real.exp (‖v‖ ^ 2 / (2 * (Module.finrank ℝ E : ℝ))) := by
  have h := gaussianPolytopeRow_vector_centered_mgf _ ν hν v
  have he : ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) ^ 2 * ‖v‖ ^ 2 / 2 =
      ‖v‖ ^ 2 / (2 * (Module.finrank ℝ E : ℝ)) := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  rwa [he] at h

end
end Nonsmooth
