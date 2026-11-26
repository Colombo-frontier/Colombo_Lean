import SecondOrder.FirstOrderEuclidean
import SecondOrder.FirstOrderScaledGeometry
import SecondOrder.BoundedLinearScaling
import SecondOrder.FiniteLossModel

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def scaledFirstOrderPopulation (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) :
    Point (FirstOrderDimension d T) → ℝ :=
  scalarLinearScaling (firstOrderChain Θ) A (firstOrderDilation d T β)

def scaledFirstOrderSample (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : Point (FirstOrderDimension d T) → ℝ :=
  scalarLinearScaling (firstOrderRandomLoss Θ z) A (firstOrderDilation d T β)

theorem scaledFirstOrderPopulation_contDiff (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) :
    ContDiff ℝ 3 (scaledFirstOrderPopulation Θ A β) :=
  scalarLinearScaling_contDiff (firstOrderChain_contDiff Θ) A _

theorem scaledFirstOrderSample_contDiff (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : ContDiff ℝ 3 (scaledFirstOrderSample Θ A β z) :=
  scalarLinearScaling_contDiff (firstOrderRandomLoss_contDiff Θ z) A _

theorem scaledFirstOrderSample_mean (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (A β R : ℝ) (hR : 2≤R) (x : Point (FirstOrderDimension d T)) :
    (∫ z, scaledFirstOrderSample Θ A β z x ∂(firstOrderChainCoefficientLaw Θ R hR).toMeasure)=
      scaledFirstOrderPopulation Θ A β x := by
  unfold scaledFirstOrderSample scaledFirstOrderPopulation scalarLinearScaling
  rw [integral_const_mul,(firstOrderRandomLoss_unbiased Θ hd R hR _).1]

/-- Only the noise is bounded in value; the public log-cosh regularizer is
handled through the population's uniform third-derivative estimate. -/
theorem scaledFirstOrderSample_C21 (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (A β R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) :
    ContDiff ℝ 2 (scaledFirstOrderSample Θ A β z) ∧ ∃ C : ℝ, 0≤C ∧
      ∀ x y, ‖hessian (scaledFirstOrderSample Θ A β z) x-hessian (scaledFirstOrderSample Θ A β z) y‖≤C*‖x-y‖ := by
  obtain ⟨hn,C,hC,hb⟩ := firstOrderChainNoise_boundedC3 Θ hd R hR z
  have hgeom := firstOrderGeometryConstant_pos.le
  let M : ℝ := firstOrderGeometryConstant*Real.sqrt d+C
  have hM : 0≤M := by dsimp [M]; positivity
  have hf := firstOrderChain_contDiff Θ
  have hthird (x : FirstOrderSpace d T) : ‖iteratedFDeriv ℝ 3 (firstOrderRandomLoss Θ z) x‖≤M := by
    change ‖iteratedFDeriv ℝ 3 (fun y => firstOrderChain Θ y+firstOrderChainNoise Θ z y) x‖≤M
    rw [iteratedFDeriv_add_apply' hf.contDiffAt hn.contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (firstOrderChain_third_bound Θ hd x) (hb x 3 le_rfl))
  let L := firstOrderDilation d T β
  have hs := scaledFirstOrderSample_contDiff Θ A β z
  refine ⟨hs.of_le (show (2:WithTop ℕ∞)≤3 by decide),|A| *‖L‖^3*M,by positivity,?_⟩
  intro x y
  apply fderiv_gradient_lipschitz_of_third_bound hs _ y x
  intro w
  exact (scalarLinearScaling_iterated_bound (firstOrderRandomLoss Θ z) A L 3
    (firstOrderRandomLoss_contDiff Θ z) w).trans
    (mul_le_mul_of_nonneg_left (hthird (L w)) (by positivity))

theorem scaledFirstOrderSample_error_bounds (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (R : ℝ) (hR : 2≤R)
    (z : FirstOrderCoefficients d T R) (x : Point (FirstOrderDimension d T)) :
    |scaledFirstOrderSample Θ A β z x-scaledFirstOrderPopulation Θ A β x|≤A*(firstOrderNoiseConstant*(R+1)) ∧
    ‖gradient (scaledFirstOrderSample Θ A β z) x-gradient (scaledFirstOrderPopulation Θ A β) x‖≤
      A*β*(firstOrderNoiseConstant*(R+1)) ∧
    ‖hessian (scaledFirstOrderSample Θ A β z) x-hessian (scaledFirstOrderPopulation Θ A β) x‖≤
      A*β^2*(firstOrderNoiseConstant*(R+1)) := by
  let L := firstOrderDilation d T β
  have hL : ‖L‖≤β := by simpa only [abs_of_nonneg hβ] using firstOrderDilation_norm d T β
  have hf := (firstOrderRandomLoss_contDiff Θ z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hg := (firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hb := firstOrderRandomLoss_error_bounds Θ hd R hR z (L x)
  refine ⟨?_,?_,?_⟩
  · change |A*firstOrderRandomLoss Θ z (L x)-A*firstOrderChain Θ (L x)|≤_
    rw [←mul_sub,abs_mul,abs_of_nonneg hA]
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
