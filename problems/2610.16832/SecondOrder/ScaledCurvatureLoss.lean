import SecondOrder.EuclideanBlocks
import SecondOrder.BoundedLinearScaling
import SecondOrder.FiniteLossModel

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

def curvatureDilation (m T : ℕ) (β : ℝ) :
    Point (CurvatureDimension m T) →L[ℝ] CurvatureSpace m T :=
  β • (curvatureCoordinates m T).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem curvatureDilation_apply (m T : ℕ) (β : ℝ) (x : Point (CurvatureDimension m T)) :
    curvatureDilation m T β x = β • curvatureCoordinates m T x := rfl

theorem curvatureDilation_norm (m T : ℕ) (β : ℝ) : ‖curvatureDilation m T β‖≤|β| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg β)
  intro x
  simp only [curvatureDilation_apply, norm_smul, Real.norm_eq_abs, curvatureCoordinates_norm, le_refl]

def scaledCurvaturePopulation (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) :
    Point (CurvatureDimension m T) → ℝ :=
  scalarLinearScaling (curvatureChain Θ) A (curvatureDilation m T β)

def scaledCurvatureSample (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : CurvatureCoefficients m T R) : Point (CurvatureDimension m T) → ℝ :=
  scalarLinearScaling (curvatureRandomLoss Θ z) A (curvatureDilation m T β)

theorem scaledCurvaturePopulation_contDiff (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) :
    ContDiff ℝ 3 (scaledCurvaturePopulation Θ A β) :=
  scalarLinearScaling_contDiff (curvatureChain_contDiff Θ) A _

theorem scaledCurvatureSample_contDiff (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : CurvatureCoefficients m T R) : ContDiff ℝ 3 (scaledCurvatureSample Θ A β z) :=
  scalarLinearScaling_contDiff (curvatureRandomLoss_contDiff Θ z) A _

theorem scaledCurvatureSample_mean (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (A β R : ℝ) (hR : 2≤R) (x : Point (CurvatureDimension m T)) :
    (∫ z, scaledCurvatureSample Θ A β z x ∂(curvatureCoefficientLaw Θ R hR).toMeasure) =
      scaledCurvaturePopulation Θ A β x := by
  unfold scaledCurvatureSample scaledCurvaturePopulation scalarLinearScaling
  rw [integral_const_mul, (curvatureRandomLoss_unbiased Θ hm R hR _).1]

theorem scaledCurvatureSample_boundedC3 (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (A β R : ℝ) (hR : 2≤R) (z : CurvatureCoefficients m T R) :
    BoundedC3 (scaledCurvatureSample Θ A β z) := by
  have hn : BoundedC3 (curvatureChainNoise Θ z) := boundedC3_reverseBlockSelector _ _
    (fun i => periodicCompletion_boundedC3 (Θ i) hm)
    (fun j _ => curvatureNoisePayload_boundedC3 Θ hm R hR z j)
  exact ((curvatureChain_boundedC3 Θ hm).add hn).scalarLinearScaling A (curvatureDilation m T β)

theorem scaledCurvatureSample_C21 (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (A β R : ℝ) (hR : 2≤R) (z : CurvatureCoefficients m T R) :
    ContDiff ℝ 2 (scaledCurvatureSample Θ A β z) ∧ ∃ C : ℝ, 0≤C ∧
      ∀ x y, ‖hessian (scaledCurvatureSample Θ A β z) x-hessian (scaledCurvatureSample Θ A β z) y‖≤C*‖x-y‖ := by
  have hf := scaledCurvatureSample_boundedC3 Θ hm A β R hR z
  obtain ⟨C,hC,hLip⟩ := hf.hessian_lipschitz
  exact ⟨hf.1.of_le (show (2:WithTop ℕ∞)≤3 by decide),C,hC,fun x y => hLip y x⟩

/-- Uniform scaled field bounds for every realized sample in the ordinary
Euclidean space of the total dimension. -/
theorem scaledCurvatureSample_error_bounds (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (R : ℝ) (hR : 2≤R)
    (z : CurvatureCoefficients m T R) (x : Point (CurvatureDimension m T)) :
    |scaledCurvatureSample Θ A β z x-scaledCurvaturePopulation Θ A β x|≤A*(curvatureNoiseConstant*(R+1)) ∧
    ‖gradient (scaledCurvatureSample Θ A β z) x-gradient (scaledCurvaturePopulation Θ A β) x‖≤
      A*β*(curvatureNoiseConstant*(R+1)/Real.sqrt ((2*m:ℕ):ℝ)) ∧
    ‖hessian (scaledCurvatureSample Θ A β z) x-hessian (scaledCurvaturePopulation Θ A β) x‖≤
      A*β^2*(curvatureNoiseConstant*(R+1)/((2*m:ℕ):ℝ)) := by
  let L := curvatureDilation m T β
  have hL : ‖L‖≤β := by simpa only [abs_of_nonneg hβ] using curvatureDilation_norm m T β
  have hf := (curvatureRandomLoss_contDiff Θ z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hg := (curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hb := curvatureRandomLoss_error_bounds Θ hm R hR z (L x)
  refine ⟨?_,?_,?_⟩
  · change |A*curvatureRandomLoss Θ z (L x)-A*curvatureChain Θ (L x)|≤_
    rw [← mul_sub, abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left hb.1 hA
  · have hh := scalarLinearScaling_gradient_error hf hg A L x
    rw [abs_of_nonneg hA] at hh
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hL hA) hb.2.1
      (norm_nonneg _) (mul_nonneg hA hβ))
  · have hh := scalarLinearScaling_hessian_error hf hg A L x
    rw [abs_of_nonneg hA] at hh
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) hL 2) hA)
      hb.2.2 (norm_nonneg _) (mul_nonneg hA (sq_nonneg β)))

end
end SecondOrder
