import Nonsmooth.C2GaussianCovariance

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem c2_gaussian_unit_centered_mgf {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ) {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    let μ := gaussianPotentialLaw U
    Integrable (fun z : E => Real.exp (t * (⟪u, z⟫_ℝ - ∫ a, ⟪u, a⟫_ℝ ∂μ))) μ ∧
      (∫ z : E, Real.exp (t * (⟪u, z⟫_ℝ - ∫ a, ⟪u, a⟫_ℝ ∂μ)) ∂μ) ≤
        Real.exp (t ^ 2 / (2 * ρ)) := by
  dsimp only
  obtain ⟨W, hW, hLaw⟩ := c2StrongQuadraticPotential_unit_marginal_exists hU hρ hu
  have hd := c2StrongQuadraticPotential_real_score_data hW
  have hI := strong_potential_centered_exp_integrable W _ hd.1 (by linarith) hd.2.1 hd.2.2 t
  have hB := c2StrongQuadraticPotential_real_centered_mgf hW (by linarith) t
  rw [← hLaw] at hI hB
  have hg : Measurable (fun z : E => ⟪u, z⟫_ℝ) := by fun_prop
  have hmean : (∫ x : ℝ, x ∂(gaussianPotentialLaw U).map (fun z : E => ⟪u, z⟫_ℝ)) =
      ∫ z, ⟪u, z⟫_ℝ ∂gaussianPotentialLaw U :=
    integral_map_of_stronglyMeasurable hg stronglyMeasurable_id
  rw [hmean] at hI hB
  have hφ : StronglyMeasurable (fun x : ℝ =>
      Real.exp (t * (x - ∫ a, ⟪u, a⟫_ℝ ∂gaussianPotentialLaw U))) :=
    (by fun_prop : Continuous (fun x : ℝ =>
      Real.exp (t * (x - ∫ a, ⟪u, a⟫_ℝ ∂gaussianPotentialLaw U)))).stronglyMeasurable
  refine ⟨(integrable_map_measure hφ.aestronglyMeasurable hg.aemeasurable).mp hI, ?_⟩
  rw [integral_map_of_stronglyMeasurable hg hφ] at hB
  exact hB

theorem c2_gaussian_direction_centered_mgf {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ) (v : E) (t : ℝ) :
    let μ := gaussianPotentialLaw U
    Integrable (fun z : E => Real.exp (t * (⟪v, z⟫_ℝ - ∫ a, ⟪v, a⟫_ℝ ∂μ))) μ ∧
      (∫ z : E, Real.exp (t * (⟪v, z⟫_ℝ - ∫ a, ⟪v, a⟫_ℝ ∂μ)) ∂μ) ≤
        Real.exp (t ^ 2 * ‖v‖ ^ 2 / (2 * ρ)) := by
  dsimp only
  letI : IsProbabilityMeasure (gaussianPotentialLaw U) := c2_gaussian_probability hU hρ
  by_cases hv0 : v = 0
  · subst v
    simp
  · let u := ‖v‖⁻¹ • v
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_eq_abs, hn]
    have hv : v = ‖v‖ • u := by simp [u, smul_smul, hn]
    have he : (fun z : E => ⟪v, z⟫_ℝ) = fun z => ‖v‖ * ⟪u, z⟫_ℝ := by
      funext z
      conv_lhs => rw [hv, inner_smul_left]
      rfl
    have h := c2_gaussian_unit_centered_mgf hU hρ hu (t * ‖v‖)
    try dsimp only at h
    have hfun : (fun z : E => Real.exp (t * (⟪v, z⟫_ℝ - ∫ a, ⟪v, a⟫_ℝ ∂gaussianPotentialLaw U))) =
        fun z => Real.exp ((t * ‖v‖) * (⟪u, z⟫_ℝ - ∫ a, ⟪u, a⟫_ℝ ∂gaussianPotentialLaw U)) := by
      rw [he, integral_const_mul]
      funext z
      rw [congrFun he z]
      congr 1
      ring
    rw [hfun]
    simpa only [mul_pow] using h

end
end Nonsmooth
