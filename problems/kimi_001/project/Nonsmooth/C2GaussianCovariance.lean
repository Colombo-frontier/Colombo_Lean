import Nonsmooth.C2GaussianUnitMarginal
import Nonsmooth.ScalarC2PotentialConcentration
import Nonsmooth.ConditionalImage

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem c2_gaussian_unit_moments {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ) {v : E} (hv : ‖v‖ = 1) :
    MemLp (fun z : E => ⟪v, z⟫_ℝ) 2 (gaussianPotentialLaw U) ∧
      variance (fun z : E => ⟪v, z⟫_ℝ) (gaussianPotentialLaw U) ≤ ρ⁻¹ := by
  obtain ⟨W, hW, hLaw⟩ := c2StrongQuadraticPotential_unit_marginal_exists hU hρ hv
  have hm : Measurable (fun z : E => ⟪v, z⟫_ℝ) := by fun_prop
  have hi := (c2StrongQuadraticPotential_real_probability_and_memLp hW (by linarith)).2
  rw [← hLaw] at hi
  refine ⟨(memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mp hi, ?_⟩
  have h := c2StrongQuadraticPotential_real_variance hW (by linarith)
  rw [← hLaw] at h
  rw [variance_map_measurable (gaussianPotentialLaw U) (fun z : E => ⟪v, z⟫_ℝ) hm
    (fun x : ℝ => x) (show Measurable (fun x : ℝ => x) from measurable_id)] at h
  exact h

theorem c2_gaussian_directional_covariance {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ) (gaussianPotentialLaw U) ≤ ‖v‖ ^ 2 / ρ := by
  by_cases hv0 : v = 0
  · subst v
    simp only [inner_zero_left, variance_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
    change variance (0 : E → ℝ) (gaussianPotentialLaw U) ≤ 0
    rw [variance_zero]
  · let u := ‖v‖⁻¹ • v
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_eq_abs, hn]
    have hv : v = ‖v‖ • u := by simp [u, smul_smul, hn]
    have he : (fun z : E => ⟪v, z⟫_ℝ) = fun z => ‖v‖ * ⟪u, z⟫_ℝ := by
      funext z
      conv_lhs => rw [hv, inner_smul_left]
      rfl
    rw [he, variance_const_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (c2_gaussian_unit_moments hU hρ hu).2 (sq_nonneg ‖v‖)

theorem c2_gaussian_vector_memLp {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ) :
    MemLp (fun z : E => z) 2 (gaussianPotentialLaw U) := by
  let b := stdOrthonormalBasis ℝ E
  have hi : Integrable (fun z : E => ∑ i, ⟪b i, z⟫_ℝ ^ 2) (gaussianPotentialLaw U) :=
    integrable_finsetSum _ (fun i _ =>
      (c2_gaussian_unit_moments hU hρ (b.orthonormal.1 i)).1.integrable_sq)
  apply (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
  apply hi.congr
  apply Eventually.of_forall
  intro z
  simpa only [real_inner_comm z, ← pow_two, real_inner_self_eq_norm_sq, id_eq] using b.sum_inner_mul_inner z z

theorem c2_gaussian_probability {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ) :
    IsProbabilityMeasure (gaussianPotentialLaw U) := by
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let v := stdOrthonormalBasis ℝ E i
  have hv : ‖v‖ = 1 := (stdOrthonormalBasis ℝ E).orthonormal.1 i
  obtain ⟨W, hW, hLaw⟩ := c2StrongQuadraticPotential_unit_marginal_exists hU hρ hv
  letI : IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-W x))) :=
    (c2StrongQuadraticPotential_real_probability_and_memLp hW (by linarith)).1
  have h := congrArg (fun μ : Measure ℝ => μ univ) hLaw
  try dsimp only at h
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
    measure_univ (μ := realDensityLaw (fun x => Real.exp (-W x)))] at h
  exact ⟨h⟩

end
end Nonsmooth
