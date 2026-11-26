import SecondOrder.CoefficientLaw
import SecondOrder.CommonRandomnessEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Information bound for the full joint response to a coefficient array.
The same map may simultaneously return a value, gradient, and Hessian. -/
theorem coefficientResponse_kl {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R) (hc : ∀ i, c i^2 = 1)
    (Φ : (ι → SignedCoefficient R) → B) :
    klDiv ((finitePiPMF (fun i => coefficientPMF R (c i) hR (hc i))).toMeasure.map Φ)
      ((finitePiPMF (fun _ : ι => fairCoefficientPMF R hR)).toMeasure.map Φ) ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)/R^2) :=
  (klDiv_finite_response _ _
    (finitePiPMF_ne_zero _ (fun i => coefficientPMF_ne_zero R (c i) hR (hc i)))
    (finitePiPMF_ne_zero _ (fun _ => fairCoefficientPMF_ne_zero R hR)) Φ).trans
      (klDiv_coefficientProduct R c hR hc)

/-- Only the new array changes between the true and reference experiments.
The common past array law is preserved and contributes no KL cost. -/
theorem coefficientResponse_with_past_kl {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (r : PMF A) (hr : ∀ a, r a ≠ 0)
    (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R) (hc : ∀ i, c i^2 = 1)
    (Φ : A × (ι → SignedCoefficient R) → B) :
    klDiv ((r.toMeasure.prod
        (finitePiPMF (fun i => coefficientPMF R (c i) hR (hc i))).toMeasure).map Φ)
      ((r.toMeasure.prod
        (finitePiPMF (fun _ : ι => fairCoefficientPMF R hR)).toMeasure).map Φ) ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)/R^2) :=
  (klDiv_common_response r _ _ hr
    (finitePiPMF_ne_zero _ (fun i => coefficientPMF_ne_zero R (c i) hR (hc i)))
    (finitePiPMF_ne_zero _ (fun _ => fairCoefficientPMF_ne_zero R hR)) Φ).trans
      (klDiv_coefficientProduct R c hR hc)

def coefficientPotential {R : ℝ} (φ : ι → ℝ) (z : ι → SignedCoefficient R) : ℝ :=
  ∑ i, (z i).1*φ i

/-- Finite-feature coefficient sampling is exactly unbiased at every point. -/
theorem coefficientPotential_mean (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R)
    (hc : ∀ i, c i^2 = 1) (φ : ι → ℝ) :
    (∫ z, coefficientPotential φ z
      ∂(finitePiPMF (fun i => coefficientPMF R (c i) hR (hc i))).toMeasure) = ∑ i, c i*φ i := by
  rw [show coefficientPotential φ = (fun z : ι → SignedCoefficient R => ∑ i, (z i).1*φ i) by rfl,
    integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const, coefficientProduct_coordinate_mean]

theorem centeredCoefficientPotential_mean (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R)
    (hc : ∀ i, c i^2 = 1) (φ : ι → ℝ) :
    (∫ z, (coefficientPotential φ z-∑ i, c i*φ i)
      ∂(finitePiPMF (fun i => coefficientPMF R (c i) hR (hc i))).toMeasure) = 0 := by
  rw [integral_sub Integrable.of_finite (integrable_const _), coefficientPotential_mean]
  simp

end
end SecondOrder
