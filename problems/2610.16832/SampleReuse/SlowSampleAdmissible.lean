import SampleReuse.FiniteAdmissible
import SampleReuse.SlowSampleSmoothness
import SampleReuse.PopulationGradient

/-! Admissibility of the concrete conservative sign chain under explicit scales. -/

open MeasureTheory SecondOrder
namespace SampleReuse
noncomputable section
variable {d T : ℕ}

/-- The paper's actual slow-coordinate sampled loss satisfies every field of
Admissible once these scalar scale inequalities hold. No regularity or oracle
property is assumed as a certificate; they are derived from the scalar loss. -/
theorem slow_sample_admissible (P : Parameters) (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) (hR : 2 ≤ R)
    (hgap : 20 * A * (T + 1 : ℕ) ≤ P.gap)
    (hL₁ : A * (Real.sqrt d)⁻¹ *
      (firstOrderGeometryConstant + firstOrderNoiseConstant * (R + 1)) ≤ P.gradientLip)
    (hL₂ : A * slowDilation d *
      (firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1)) ≤ P.hessianLip)
    (hσg : A * slowDilation d * (firstOrderNoiseConstant * (R + 1)) ≤ P.gradientNoise)
    (hσH : A * (Real.sqrt d)⁻¹ * (firstOrderNoiseConstant * (R + 1)) ≤ P.hessianNoise)
    (hG : A * slowDilation d * (20 + 40 * completionDerivativeBound) *
      Real.sqrt (T + 1 : ℕ) ≤ P.gradientBound) :
    Admissible (firstOrderChainCoefficientLaw Θ R hR).toMeasure P
      (scaledFirstOrderPopulation Θ A (slowDilation d))
      (scaledFirstOrderSample Θ A (slowDilation d)) 0 := by
  have hβ : 0 ≤ slowDilation d := inv_nonneg.mpr (slowAlpha_pos hd).le
  apply finite_admissible_of_uniform_bounds
    (firstOrderChainCoefficientLaw Θ R hR) P _ _ 0
  · intro z
    exact (scaledFirstOrderSample_contDiff Θ A (slowDilation d) z).of_le
      (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  · exact scaledFirstOrderSample_mean Θ hd A (slowDilation d) R hR
  · intro x
    exact (scaledFirstOrderPopulation_gap Θ hA (slowDilation d) x).trans hgap
  · intro z x y
    exact (slow_sample_gradient_lipschitz Θ hd hA R hR z x y).trans
      (mul_le_mul_of_nonneg_right hL₁ (norm_nonneg _))
  · intro z x y
    exact (slow_sample_hessian_lipschitz Θ hd hA R hR z x y).trans
      (mul_le_mul_of_nonneg_right hL₂ (norm_nonneg _))
  · intro z x
    exact ((scaledFirstOrderSample_error_bounds Θ hd hA hβ R hR z x).2.1).trans hσg
  · intro z x
    have hh := (scaledFirstOrderSample_error_bounds Θ hd hA hβ R hR z x).2.2
    rw [slowDilation_sq] at hh
    exact hh.trans hσH
  · intro x
    exact (slow_population_gradient_bound Θ hd hA x).trans hG

end
end SampleReuse
