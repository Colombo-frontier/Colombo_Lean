import Nonsmooth.C2StrongQuadraticPotential
import Nonsmooth.StrongPotentialMGF

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem c2StrongQuadraticPotential_real_score_data {U : ℝ → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) :
    Continuous (fun x => fderiv ℝ U x 1) ∧
    (∀ x, HasDerivAt U (fderiv ℝ U x 1) x) ∧
    Monotone (fun x => fderiv ℝ U x 1 - ρ * x) := by
  have hd := contDiff_two_derivative_data U hU.smooth
  refine ⟨hd.2.2.1.clm_apply continuous_const, fun x => (hd.1 x).hasDerivAt, ?_⟩
  have hs (x : ℝ) : HasDerivAt (fun y => fderiv ℝ U y 1) (fderiv ℝ (fderiv ℝ U) x 1 1) x :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasFDerivAt.comp_hasDerivAt x (hd.2.1 x).hasDerivAt
  apply monotone_of_hasDerivAt_nonneg
    (fun x => (hs x).sub ((hasDerivAt_id x).const_mul ρ))
  intro x
  change (0 : ℝ) ≤ fderiv ℝ (fderiv ℝ U) x 1 1 - ρ * 1
  have hh := hU.hessian_lower x 1
  norm_num only [norm_one, one_pow, mul_one] at hh ⊢
  linarith

theorem c2StrongQuadraticPotential_real_probability_and_memLp {U : ℝ → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-U x))) ∧
      MemLp (fun x : ℝ => x) 2 (realDensityLaw (fun x => Real.exp (-U x))) := by
  have hd := c2StrongQuadraticPotential_real_score_data hU
  exact strong_potential_law_probability_and_memLp U _ hd.1 hρ hd.2.1 hd.2.2

theorem c2StrongQuadraticPotential_real_variance {U : ℝ → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 0 < ρ) :
    variance (fun x : ℝ => x) (realDensityLaw (fun x => Real.exp (-U x))) ≤ ρ⁻¹ := by
  have hd := c2StrongQuadraticPotential_real_score_data hU
  exact strong_potential_law_variance U _ hd.1 hρ hd.2.1 hd.2.2

theorem c2StrongQuadraticPotential_real_centered_mgf {U : ℝ → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 0 < ρ) (t : ℝ) :
    (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂realDensityLaw (fun y => Real.exp (-U y))))
      ∂realDensityLaw (fun x => Real.exp (-U x))) ≤ Real.exp (t ^ 2 / (2 * ρ)) := by
  have hd := c2StrongQuadraticPotential_real_score_data hU
  exact strong_potential_centered_mgf U _ hd.1 hρ hd.2.1 hd.2.2 t

end
end Nonsmooth
