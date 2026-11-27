import Nonsmooth.ParametricPotentialExpectation
import Nonsmooth.CovarianceExhaustion

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- The derivative of the actual slice barycenter is minus the coordinate-score
covariance; both differentiated integrals have explicit local domination. -/
theorem potentialRegression_derivative (V s : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : ∀ r, Measurable (V r)) (hi : ∀ r, Integrable (fun x => Real.exp (-V r x)))
    (hnum : PotentialMomentRegularAt V s (fun _ x => x) (fun _ _ => 0) t)
    (hden : PotentialMomentRegularAt V s (fun _ _ => 1) (fun _ _ => 0) t)
    (hx2 : MemLp (fun x : ℝ => x) 2 (realDensityLaw (fun x => Real.exp (-V t x))))
    (hs2 : MemLp (s t) 2 (realDensityLaw (fun x => Real.exp (-V t x)))) :
    HasDerivAt (potentialExpectation V (fun _ x => x))
      (-(∫ x, x * (s t x - ∫ y, s t y ∂realDensityLaw (fun y => Real.exp (-V t y)))
        ∂realDensityLaw (fun x => Real.exp (-V t x)))) t := by
  have hd := potentialExpectation_derivative V s (fun _ x => x) (fun _ _ => 0) t hV hi hnum hden
  convert hd using 1
  dsimp only [potentialExpectation]
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-V t x) := (Real.exp_pos _).le
  letI : IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-V t x))) :=
    realDensityLaw_probability _ (hi t) hw0 (integral_exp_pos (hi t))
  rw [integral_mul_centered_eq _ (s t) (fun x : ℝ => x)
    (hx2.integrable (by norm_num)) (hx2.integrable_mul hs2)]
  simp only [zero_sub, integral_neg]
  ring

/-- Differentiating the normalized score gives marginal curvature as the mean
second derivative minus the score variance. -/
theorem potentialScore_derivative (V s γ : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : ∀ r, Measurable (V r)) (hi : ∀ r, Integrable (fun x => Real.exp (-V r x)))
    (hnum : PotentialMomentRegularAt V s s γ t)
    (hden : PotentialMomentRegularAt V s (fun _ _ => 1) (fun _ _ => 0) t)
    (hs2 : MemLp (s t) 2 (realDensityLaw (fun x => Real.exp (-V t x))))
    (hγ : Integrable (γ t) (realDensityLaw (fun x => Real.exp (-V t x)))) :
    HasDerivAt (potentialExpectation V s)
      (potentialExpectation V γ t - variance (s t) (realDensityLaw (fun x => Real.exp (-V t x)))) t := by
  letI : IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-V t x))) :=
    realDensityLaw_probability _ (hi t) (fun _ => (Real.exp_pos _).le) (integral_exp_pos (hi t))
  have hd := potentialExpectation_derivative V s s γ t hV hi hnum hden
  convert hd using 1
  dsimp only [potentialExpectation]
  rw [variance_eq_sub hs2]
  simp only [Pi.pow_apply]
  rw [integral_sub (f := γ t) (g := fun x => s t x * s t x) hγ (hs2.integrable_mul hs2)]
  simp only [← pow_two]
  ring

theorem potentialNegativeLogPartition_secondDerivative (V s γ : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : ∀ r, Measurable (V r)) (hi : ∀ r, Integrable (fun x => Real.exp (-V r x)))
    (hnum : PotentialMomentRegularAt V s s γ t)
    (hden : ∀ r, PotentialMomentRegularAt V s (fun _ _ => 1) (fun _ _ => 0) r)
    (hs2 : MemLp (s t) 2 (realDensityLaw (fun x => Real.exp (-V t x))))
    (hγ : Integrable (γ t) (realDensityLaw (fun x => Real.exp (-V t x)))) :
    HasDerivAt (deriv (fun r => -Real.log (potentialPartition V r)))
      (potentialExpectation V γ t - variance (s t) (realDensityLaw (fun x => Real.exp (-V t x)))) t := by
  have he : deriv (fun r => -Real.log (potentialPartition V r)) = potentialExpectation V s := by
    funext r
    exact (potentialNegativeLogPartition_derivative V s r (hV r) (hi r) (hden r)).deriv
  rw [he]
  exact potentialScore_derivative V s γ t hV hi hnum (hden t) hs2 hγ

end
end Nonsmooth
