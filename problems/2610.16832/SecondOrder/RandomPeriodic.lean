import SecondOrder.PeriodicFourier
import SecondOrder.CoefficientResponse
import SecondOrder.FiniteMeanCalculus

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {d : ℕ}

def periodicCoefficientLaw (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R) :
    PMF (UpperPair d → SignedCoefficient R) :=
  finitePiPMF (fun e => coefficientPMF R (pairSign θ e) hR (pairSign_sq θ e))

/-- A single smooth scalar loss with the original real-valued random coefficients. -/
def sampledPeriodicPotential {R : ℝ} (z : UpperPair d → SignedCoefficient R) : Point d → ℝ :=
  fourierPotential (fun e => (z e).1)

theorem sampledPeriodicPotential_contDiff {R : ℝ} (z : UpperPair d → SignedCoefficient R)
    (k : WithTop ℕ∞) : ContDiff ℝ k (sampledPeriodicPotential z) :=
  fourierPotential_contDiff _ k

theorem sampledPeriodicPotential_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R) (x : Point d) :
    (∫ z, sampledPeriodicPotential z x ∂(periodicCoefficientLaw θ R hR).toMeasure) =
      fourierPotential (pairSign θ) x := by
  unfold sampledPeriodicPotential fourierPotential
  rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const_mul]
  have he := coefficientPotential_mean R (pairSign θ) hR (pairSign_sq θ)
    (fun e => Real.cos (x e.1.1-x e.1.2))
  change (∫ z, pairCosPotential (fun e => (z e).1) x
    ∂(periodicCoefficientLaw θ R hR).toMeasure) = pairCosPotential (pairSign θ) x at he
  rw [he]
  simp

theorem sampledPeriodicPotential_iteratedFDeriv_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R)
    (k : ℕ) (x : Point d) :
    (∫ z, iteratedFDeriv ℝ k (sampledPeriodicPotential z) x
      ∂(periodicCoefficientLaw θ R hR).toMeasure) =
      iteratedFDeriv ℝ k (fourierPotential (pairSign θ)) x := by
  rw [← iteratedFDeriv_finiteMean _ _ _ _ (fun z => sampledPeriodicPotential_contDiff z k)]
  rw [show (fun y => ∫ z, sampledPeriodicPotential z y
    ∂(periodicCoefficientLaw θ R hR).toMeasure) = fourierPotential (pairSign θ) from
      funext (sampledPeriodicPotential_mean θ R hR)]

theorem sampledPeriodicPotential_gradient_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R)
    (x : Point d) :
    (∫ z, gradient (sampledPeriodicPotential z) x
      ∂(periodicCoefficientLaw θ R hR).toMeasure) =
      gradient (fourierPotential (pairSign θ)) x := by
  rw [← gradient_finiteMean _ _ _ (fun z =>
    (sampledPeriodicPotential_contDiff z 1).differentiable (by norm_num) x)]
  rw [show (fun y => ∫ z, sampledPeriodicPotential z y
    ∂(periodicCoefficientLaw θ R hR).toMeasure) = fourierPotential (pairSign θ) from
      funext (sampledPeriodicPotential_mean θ R hR)]

theorem sampledPeriodicPotential_hessian_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R)
    (x : Point d) :
    (∫ z, hessian (sampledPeriodicPotential z) x
      ∂(periodicCoefficientLaw θ R hR).toMeasure) =
      hessian (fourierPotential (pairSign θ)) x := by
  unfold hessian
  rw [← fderiv_gradient_finiteMean _ _ _ (fun z => sampledPeriodicPotential_contDiff z 2)]
  rw [show (fun y => ∫ z, sampledPeriodicPotential z y
    ∂(periodicCoefficientLaw θ R hR).toMeasure) = fourierPotential (pairSign θ) from
      funext (sampledPeriodicPotential_mean θ R hR)]

/-- The value, gradient and Hessian of the same sampled loss are jointly unbiased. -/
theorem periodicBlock_sample_unbiased {m : ℕ} (θ : BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (x : Point (2*m)) :
    (∫ z, sampledPeriodicPotential z x ∂(periodicCoefficientLaw θ.1 R hR).toMeasure) =
      periodicBlockPotential θ x ∧
    (∫ z, gradient (sampledPeriodicPotential z) x ∂(periodicCoefficientLaw θ.1 R hR).toMeasure) =
      gradient (periodicBlockPotential θ) x ∧
    (∫ z, hessian (sampledPeriodicPotential z) x ∂(periodicCoefficientLaw θ.1 R hR).toMeasure) =
      hessian (periodicBlockPotential θ) x := by
  rw [periodicBlockPotential_fourier θ hm]
  exact ⟨sampledPeriodicPotential_mean _ _ _ _, sampledPeriodicPotential_gradient_mean _ _ _ _,
    sampledPeriodicPotential_hessian_mean _ _ _ _⟩

theorem signedCoefficient_abs (R : ℝ) (hR : 0 ≤ R) (z : SignedCoefficient R) : |z.1| = R := by
  rcases z.2 with h | h
  · rw [h, abs_neg, abs_of_nonneg hR]
  · have he : z.1 = R := by simpa using h
    rw [he, abs_of_nonneg hR]

theorem periodicCoefficient_error_bound (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R)
    (z : UpperPair d → SignedCoefficient R) (e : UpperPair d) :
    |(z e).1-pairSign θ e| ≤ R+1 := by
  have hs : |pairSign θ e| = 1 := by
    nlinarith [sq_abs (pairSign θ e), pairSign_sq θ e, abs_nonneg (pairSign θ e)]
  exact (abs_sub _ _).trans_eq (by rw [signedCoefficient_abs R (by linarith), hs])

/-- The actual simultaneous value/gradient/Hessian response of the sampled scalar potential. -/
def periodicSampleJet {R : ℝ} (x : Point d) (z : UpperPair d → SignedCoefficient R) :
    ℝ × Point d × (Point d →L[ℝ] Point d) :=
  (sampledPeriodicPotential z x, gradient (sampledPeriodicPotential z) x,
    hessian (sampledPeriodicPotential z) x)

/-- Data processing applies to the complete continuous-valued block response. -/
theorem periodicSampleJet_kl (θ : Fin d → Bool) (R : ℝ) (hR : 2 ≤ R) (x : Point d) :
    klDiv ((periodicCoefficientLaw θ R hR).toMeasure.map (periodicSampleJet x))
      ((finitePiPMF (fun _ : UpperPair d => fairCoefficientPMF R hR)).toMeasure.map
        (periodicSampleJet x)) ≤ ENNReal.ofReal ((d:ℝ)*((d:ℝ)-1)/(2*R^2)) := by
  have he := coefficientResponse_kl R (pairSign θ) hR (pairSign_sq θ) (periodicSampleJet x)
  rw [upperPair_card_real] at he
  convert he using 1 <;> congr 1 <;> ring

end
end SecondOrder
