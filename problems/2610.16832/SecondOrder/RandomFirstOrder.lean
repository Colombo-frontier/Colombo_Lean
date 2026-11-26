import SecondOrder.FirstOrderCompletionRegularity
import SecondOrder.CoefficientResponse
import SecondOrder.FiniteMeanCalculus

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def firstOrderBlockPotential (θ : Fin d → Bool) (x : Point d) : ℝ :=
  -2*(3+firstOrderBlockEncoding θ x)

theorem firstOrderBlockPotential_contDiff (θ : Fin d → Bool) (k : WithTop ℕ∞) :
    ContDiff ℝ k (firstOrderBlockPotential θ) :=
  contDiff_const.mul (contDiff_const.add (firstOrderBlockEncoding_contDiff θ k))

@[simp] theorem firstOrderBlockPotential_zero (θ : Fin d → Bool) :
    firstOrderBlockPotential θ 0 = -6 := by
  simp [firstOrderBlockPotential,firstOrderBlockEncoding]
  <;> norm_num

theorem firstOrderBlockPotential_range (θ : Fin d → Bool) (x : Point d) :
    -10≤firstOrderBlockPotential θ x ∧ firstOrderBlockPotential θ x≤-2 := by
  have hh := abs_le.mp (firstOrderBlockEncoding_abs_le θ x)
  dsimp [firstOrderBlockPotential]
  constructor <;> linarith

def firstOrderCoefficientLaw (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R) :
    PMF (Fin d → SignedCoefficient R) :=
  finitePiPMF (fun i => coefficientPMF R (signValue (θ i)) hR (signValue_sq (θ i)))

/-- A sampled scalar potential; all oracle components below are its actual derivatives. -/
def sampledFirstOrderPotential {R : ℝ} (z : Fin d → SignedCoefficient R) (x : Point d) : ℝ :=
  -2*(3+firstOrderCoefficientEncoding (fun i => (z i).1) x)

theorem sampledFirstOrderPotential_contDiff {R : ℝ} (z : Fin d → SignedCoefficient R)
    (k : WithTop ℕ∞) : ContDiff ℝ k (sampledFirstOrderPotential z) :=
  contDiff_const.mul (contDiff_const.add (firstOrderCoefficientEncoding_contDiff _ k))

theorem firstOrderCoefficientEncoding_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R) (x : Point d) :
    (∫ z, firstOrderCoefficientEncoding (fun i => (z i).1) x
      ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=firstOrderBlockEncoding θ x := by
  have he := coefficientPotential_mean R (fun i => signValue (θ i)) hR
    (fun i => signValue_sq (θ i)) (fun i => (2/(d:ℝ))*Real.tanh (Real.sqrt d*x i))
  convert he using 1 <;>
    simp only [firstOrderCoefficientEncoding,firstOrderBlockEncoding,separablePotential,
      coefficientPotential,firstOrderCoefficientLaw,mul_left_comm,mul_comm,mul_assoc]

theorem sampledFirstOrderPotential_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R) (x : Point d) :
    (∫ z, sampledFirstOrderPotential z x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=
      firstOrderBlockPotential θ x := by
  unfold sampledFirstOrderPotential
  rw [integral_const_mul,integral_add (integrable_const _) Integrable.of_finite,
    integral_const,firstOrderCoefficientEncoding_mean]
  simp [firstOrderBlockPotential]

theorem sampledFirstOrderPotential_iteratedFDeriv_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R)
    (k : ℕ) (x : Point d) :
    (∫ z, iteratedFDeriv ℝ k (sampledFirstOrderPotential z) x
      ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=iteratedFDeriv ℝ k (firstOrderBlockPotential θ) x := by
  rw [←iteratedFDeriv_finiteMean _ _ _ _ (fun z => sampledFirstOrderPotential_contDiff z k)]
  rw [show (fun y => ∫ z, sampledFirstOrderPotential z y
    ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=firstOrderBlockPotential θ from
      funext (sampledFirstOrderPotential_mean θ R hR)]

theorem sampledFirstOrderPotential_gradient_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R)
    (x : Point d) :
    (∫ z, gradient (sampledFirstOrderPotential z) x
      ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=gradient (firstOrderBlockPotential θ) x := by
  rw [←gradient_finiteMean _ _ _ (fun z =>
    (sampledFirstOrderPotential_contDiff z 1).differentiable (by norm_num) x)]
  rw [show (fun y => ∫ z, sampledFirstOrderPotential z y
    ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=firstOrderBlockPotential θ from
      funext (sampledFirstOrderPotential_mean θ R hR)]

theorem sampledFirstOrderPotential_hessian_mean (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R)
    (x : Point d) :
    (∫ z, hessian (sampledFirstOrderPotential z) x
      ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=hessian (firstOrderBlockPotential θ) x := by
  unfold hessian
  rw [←fderiv_gradient_finiteMean _ _ _ (fun z => sampledFirstOrderPotential_contDiff z 2)]
  rw [show (fun y => ∫ z, sampledFirstOrderPotential z y
    ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=firstOrderBlockPotential θ from
      funext (sampledFirstOrderPotential_mean θ R hR)]

theorem firstOrderBlock_sample_unbiased (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R) (x : Point d) :
    (∫ z, sampledFirstOrderPotential z x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=
      firstOrderBlockPotential θ x ∧
    (∫ z, gradient (sampledFirstOrderPotential z) x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=
      gradient (firstOrderBlockPotential θ) x ∧
    (∫ z, hessian (sampledFirstOrderPotential z) x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=
      hessian (firstOrderBlockPotential θ) x :=
  ⟨sampledFirstOrderPotential_mean _ _ _ _,sampledFirstOrderPotential_gradient_mean _ _ _ _,
    sampledFirstOrderPotential_hessian_mean _ _ _ _⟩

def firstOrderSampleJet {R : ℝ} (x : Point d) (z : Fin d → SignedCoefficient R) :
    ℝ × Point d × (Point d →L[ℝ] Point d) :=
  (sampledFirstOrderPotential z x,gradient (sampledFirstOrderPotential z) x,
    hessian (sampledFirstOrderPotential z) x)

/-- The complete value/gradient/Hessian response costs at most D/R² in relative entropy. -/
theorem firstOrderSampleJet_kl (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R) (x : Point d) :
    klDiv ((firstOrderCoefficientLaw θ R hR).toMeasure.map (firstOrderSampleJet x))
      ((finitePiPMF (fun _ : Fin d => fairCoefficientPMF R hR)).toMeasure.map
        (firstOrderSampleJet x))≤ENNReal.ofReal ((d:ℝ)/R^2) := by
  simpa only [Fintype.card_fin] using coefficientResponse_kl R (fun i => signValue (θ i)) hR
    (fun i => signValue_sq (θ i)) (firstOrderSampleJet x)

end
end SecondOrder
