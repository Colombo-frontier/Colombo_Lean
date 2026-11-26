import SecondOrder.RandomFirstOrder
import SecondOrder.RandomPeriodic
import SecondOrder.ContinuousChord

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def firstOrderBlockNoise (θ : Fin d → Bool) {R : ℝ}
    (z : Fin d → SignedCoefficient R) (x : Point d) : ℝ :=
  sampledFirstOrderPotential z x-firstOrderBlockPotential θ x

theorem firstOrderBlockNoise_eq (θ : Fin d → Bool) {R : ℝ}
    (z : Fin d → SignedCoefficient R) :
    firstOrderBlockNoise θ z=firstOrderCoefficientEncoding (fun i => -2*((z i).1-signValue (θ i))) := by
  funext x
  unfold firstOrderBlockNoise sampledFirstOrderPotential firstOrderBlockPotential
    firstOrderBlockEncoding firstOrderCoefficientEncoding separablePotential
  have he : (∑ i, (2/(d:ℝ))*(-2*((z i).1-signValue (θ i)))*Real.tanh (Real.sqrt d*x i))=
      -2*((∑ i, (2/(d:ℝ))*(z i).1*Real.tanh (Real.sqrt d*x i))-
        ∑ i, (2/(d:ℝ))*signValue (θ i)*Real.tanh (Real.sqrt d*x i)) := by
    rw [Finset.sum_sub_distrib.symm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem firstOrderBlockNoise_contDiff (θ : Fin d → Bool) {R : ℝ}
    (z : Fin d → SignedCoefficient R) (k : WithTop ℕ∞) : ContDiff ℝ k (firstOrderBlockNoise θ z) :=
  (sampledFirstOrderPotential_contDiff z k).sub (firstOrderBlockPotential_contDiff θ k)

theorem firstOrderCoefficient_error_bound (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R)
    (z : Fin d → SignedCoefficient R) (i : Fin d) : |(z i).1-signValue (θ i)|≤R+1 := by
  have hs : |signValue (θ i)|=1 := by cases hi : θ i <;> norm_num [hi,signValue]
  exact (abs_sub _ _).trans_eq (by rw [signedCoefficient_abs R (by linarith),hs])

theorem firstOrderBlockNoise_coefficient_bound (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R)
    (z : Fin d → SignedCoefficient R) (i : Fin d) : |-2*((z i).1-signValue (θ i))|≤2*(R+1) := by
  simpa only [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)] using
    mul_le_mul_of_nonneg_left (firstOrderCoefficient_error_bound θ R hR z i) (by norm_num : (0:ℝ)≤2)

theorem firstOrderBlockNoise_gradient (θ : Fin d → Bool) {R : ℝ}
    (z : Fin d → SignedCoefficient R) :
    gradient (firstOrderBlockNoise θ z)=
      fun x => gradient (sampledFirstOrderPotential z) x-gradient (firstOrderBlockPotential θ) x := by
  funext x
  change (InnerProductSpace.toDual ℝ (Point d)).symm
    (fderiv ℝ (fun y => sampledFirstOrderPotential z y-firstOrderBlockPotential θ y) x)=_
  rw [fderiv_sub ((sampledFirstOrderPotential_contDiff z 1).differentiable (by norm_num) x)
    ((firstOrderBlockPotential_contDiff θ 1).differentiable (by norm_num) x),map_sub]
  rfl

theorem firstOrderBlockNoise_hessian (θ : Fin d → Bool) {R : ℝ}
    (z : Fin d → SignedCoefficient R) (x : Point d) :
    hessian (firstOrderBlockNoise θ z) x=
      hessian (sampledFirstOrderPotential z) x-hessian (firstOrderBlockPotential θ) x := by
  rw [hessian,firstOrderBlockNoise_gradient]
  exact fderiv_sub
    ((contDiff_gradient_one (sampledFirstOrderPotential_contDiff z 2)).differentiable (by norm_num) x)
    ((contDiff_gradient_one (firstOrderBlockPotential_contDiff θ 2)).differentiable (by norm_num) x)

/-- Uniform errors of the actual centered scalar potential and its first three derivatives. -/
theorem firstOrderBlockNoise_bounds (θ : Fin d → Bool) (hd : 0<d) (R : ℝ) (hR : 2≤R)
    (z : Fin d → SignedCoefficient R) (x : Point d) :
    |firstOrderBlockNoise θ z x|≤4*(R+1) ∧
    ‖gradient (firstOrderBlockNoise θ z) x‖≤4*(R+1) ∧
    ‖hessian (firstOrderBlockNoise θ z) x‖≤8*(R+1) ∧
    ‖iteratedFDeriv ℝ 3 (firstOrderBlockNoise θ z) x‖≤24*(R+1)*Real.sqrt d := by
  rw [firstOrderBlockNoise_eq]
  have ha := firstOrderBlockNoise_coefficient_bound θ R hR z
  have hp : 0≤2*(R+1) := by linarith
  refine ⟨?_,?_,?_,?_⟩
  · convert firstOrderCoefficientEncoding_value_bound _ hd hp ha x using 1 <;> ring
  · convert firstOrderCoefficientEncoding_gradient_bound _ hd hp ha x using 1 <;> ring
  · convert firstOrderCoefficientEncoding_hessian_bound _ hd hp ha x using 1 <;> ring
  · convert firstOrderCoefficientEncoding_third_bound _ hd hp ha x using 1 <;> ring

theorem firstOrderBlockNoise_hessian_lipschitz (θ : Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : Fin d → SignedCoefficient R) (x y : Point d) :
    ‖hessian (firstOrderBlockNoise θ z) y-hessian (firstOrderBlockNoise θ z) x‖≤
      (24*(R+1)*Real.sqrt d)*‖y-x‖ := by
  rw [firstOrderBlockNoise_eq]
  convert firstOrderCoefficientEncoding_hessian_lipschitz _ hd (show 0≤2*(R+1) by linarith)
    (firstOrderBlockNoise_coefficient_bound θ R hR z) x y using 1 <;> ring

theorem firstOrderBlockNoise_zero_means (θ : Fin d → Bool) (R : ℝ) (hR : 2≤R) (x : Point d) :
    (∫ z, firstOrderBlockNoise θ z x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=0 ∧
    (∫ z, gradient (firstOrderBlockNoise θ z) x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=0 ∧
    (∫ z, hessian (firstOrderBlockNoise θ z) x ∂(firstOrderCoefficientLaw θ R hR).toMeasure)=0 := by
  have hu := firstOrderBlock_sample_unbiased θ R hR x
  simp only [firstOrderBlockNoise,firstOrderBlockNoise_gradient,firstOrderBlockNoise_hessian,
    integral_sub Integrable.of_finite (integrable_const _),integral_const,
    measureReal_univ_eq_one,one_smul,hu.1,hu.2.1,hu.2.2,sub_self,and_self]

theorem firstOrderBlock_sample_error_bounds (θ : Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : Fin d → SignedCoefficient R) (x : Point d) :
    |sampledFirstOrderPotential z x-firstOrderBlockPotential θ x|≤4*(R+1) ∧
    ‖gradient (sampledFirstOrderPotential z) x-gradient (firstOrderBlockPotential θ) x‖≤4*(R+1) ∧
    ‖hessian (sampledFirstOrderPotential z) x-hessian (firstOrderBlockPotential θ) x‖≤8*(R+1) := by
  have hh := firstOrderBlockNoise_bounds θ hd R hR z x
  refine ⟨hh.1,?_,?_⟩
  · simpa only [firstOrderBlockNoise_gradient] using hh.2.1
  · simpa only [firstOrderBlockNoise_hessian] using hh.2.2.1

section Measurable
variable {R : ℝ}

private theorem measurable_firstOrder_coefficients {B : Type*} [MeasurableSpace B]
    (f : (Fin d → SignedCoefficient R) → Point d → B) (hf : ∀ z, Measurable (f z)) :
    Measurable (fun w : (Fin d → SignedCoefficient R) × Point d => f w.1 w.2) := by
  have hh : Measurable (fun w : Point d × (Fin d → SignedCoefficient R) => f w.2 w.1) :=
    measurable_from_prod_countable hf
  exact hh.comp measurable_swap

theorem sampledFirstOrderPotential_value_measurable :
    Measurable (fun w : (Fin d → SignedCoefficient R) × Point d => sampledFirstOrderPotential w.1 w.2) := by
  apply measurable_firstOrder_coefficients
  intro z
  exact (sampledFirstOrderPotential_contDiff z 0).continuous.measurable

theorem sampledFirstOrderPotential_gradient_measurable :
    Measurable (fun w : (Fin d → SignedCoefficient R) × Point d => gradient (sampledFirstOrderPotential w.1) w.2) := by
  apply measurable_firstOrder_coefficients (fun z => gradient (sampledFirstOrderPotential z))
  intro z
  exact (contDiff_gradient_one (sampledFirstOrderPotential_contDiff z 2)).continuous.measurable

theorem sampledFirstOrderPotential_hessian_measurable :
    Measurable (fun w : (Fin d → SignedCoefficient R) × Point d => hessian (sampledFirstOrderPotential w.1) w.2) := by
  apply measurable_firstOrder_coefficients (fun z => hessian (sampledFirstOrderPotential z))
  intro z
  exact (continuous_hessian (sampledFirstOrderPotential_contDiff z 2)).measurable

end Measurable
end
end SecondOrder
