import SecondOrder.RandomPeriodic
import SecondOrder.PairNoiseBounds
import SecondOrder.ContinuousChord

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {m : ℕ}

def periodicBlockNoise (θ : BalancedVector m) {R : ℝ}
    (z : UpperPair (2*m) → SignedCoefficient R) (x : Point (2*m)) : ℝ :=
  sampledPeriodicPotential z x-periodicBlockPotential θ x

theorem periodicBlockNoise_eq (θ : BalancedVector m) (hm : 0 < m) {R : ℝ}
    (z : UpperPair (2*m) → SignedCoefficient R) :
    periodicBlockNoise θ z = pairNoisePotential (fun e => (z e).1-pairSign θ.1 e) := by
  funext x
  unfold periodicBlockNoise sampledPeriodicPotential
  rw [periodicBlockPotential_fourier θ hm, fourierPotential_sub]
  rfl

theorem periodicBlockNoise_contDiff (θ : BalancedVector m) {R : ℝ}
    (z : UpperPair (2*m) → SignedCoefficient R) (k : WithTop ℕ∞) :
    ContDiff ℝ k (periodicBlockNoise θ z) :=
  (sampledPeriodicPotential_contDiff z k).sub (periodicBlockPotential_contDiff θ k)

theorem periodicBlockNoise_gradient (θ : BalancedVector m) {R : ℝ}
    (z : UpperPair (2*m) → SignedCoefficient R) :
    gradient (periodicBlockNoise θ z) =
      fun x => gradient (sampledPeriodicPotential z) x-gradient (periodicBlockPotential θ) x := by
  funext x
  change (InnerProductSpace.toDual ℝ (Point (2*m))).symm
    (fderiv ℝ (fun y => sampledPeriodicPotential z y-periodicBlockPotential θ y) x) = _
  rw [fderiv_sub ((sampledPeriodicPotential_contDiff z 1).differentiable (by norm_num) x)
    ((periodicBlockPotential_contDiff θ 1).differentiable (by norm_num) x), map_sub]
  rfl

theorem periodicBlockNoise_hessian (θ : BalancedVector m) {R : ℝ}
    (z : UpperPair (2*m) → SignedCoefficient R) (x : Point (2*m)) :
    hessian (periodicBlockNoise θ z) x =
      hessian (sampledPeriodicPotential z) x-hessian (periodicBlockPotential θ) x := by
  rw [hessian, periodicBlockNoise_gradient]
  exact fderiv_sub
    ((contDiff_gradient_one (sampledPeriodicPotential_contDiff z 2)).differentiable (by norm_num) x)
    ((contDiff_gradient_one (periodicBlockPotential_contDiff θ 2)).differentiable (by norm_num) x)

/-- Every realized block error obeys the manuscript's three uniform field bounds. -/
theorem periodicBlockNoise_bounds (θ : BalancedVector m) (hm : 0 < m) (R : ℝ) (hR : 2 ≤ R)
    (z : UpperPair (2*m) → SignedCoefficient R) (x : Point (2*m)) :
    |periodicBlockNoise θ z x| ≤ (R+1)/2 ∧
    ‖gradient (periodicBlockNoise θ z) x‖ ≤ (R+1)/Real.sqrt ((2*m:ℕ):ℝ) ∧
    ‖hessian (periodicBlockNoise θ z) x‖ ≤ (R+1)/((2*m:ℕ):ℝ) ∧
    ‖iteratedFDeriv ℝ 3 (periodicBlockNoise θ z) x‖ ≤ 2*(R+1)/((2*m:ℕ):ℝ) := by
  rw [periodicBlockNoise_eq θ hm]
  have ha := periodicCoefficient_error_bound θ.1 R hR z
  have hp : 0 ≤ R+1 := by linarith
  exact ⟨pairNoisePotential_value_bound _ (by omega) hp ha x,
    pairNoisePotential_gradient_bound _ (by omega) hp ha x,
    pairNoisePotential_hessian_bound _ (by omega) hp ha x,
    pairNoisePotential_third_bound _ (by omega) hp ha x⟩

theorem periodicBlockNoise_hessian_lipschitz (θ : BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : UpperPair (2*m) → SignedCoefficient R) (x y : Point (2*m)) :
    ‖hessian (periodicBlockNoise θ z) y-hessian (periodicBlockNoise θ z) x‖ ≤
      (2*(R+1)/((2*m:ℕ):ℝ))*‖y-x‖ := by
  rw [periodicBlockNoise_eq θ hm]
  exact pairNoisePotential_hessian_lipschitz _ (by omega) (by linarith)
    (periodicCoefficient_error_bound θ.1 R hR z) x y

theorem periodicBlockNoise_zero_means (θ : BalancedVector m) (hm : 0 < m) (R : ℝ) (hR : 2 ≤ R)
    (x : Point (2*m)) :
    (∫ z, periodicBlockNoise θ z x ∂(periodicCoefficientLaw θ.1 R hR).toMeasure) = 0 ∧
    (∫ z, gradient (periodicBlockNoise θ z) x ∂(periodicCoefficientLaw θ.1 R hR).toMeasure) = 0 ∧
    (∫ z, hessian (periodicBlockNoise θ z) x ∂(periodicCoefficientLaw θ.1 R hR).toMeasure) = 0 := by
  have hu := periodicBlock_sample_unbiased θ hm R hR x
  simp only [periodicBlockNoise, periodicBlockNoise_gradient, periodicBlockNoise_hessian,
    integral_sub Integrable.of_finite (integrable_const _), integral_const,
    measureReal_univ_eq_one, one_smul, hu.1, hu.2.1, hu.2.2, sub_self, and_self]

theorem periodicBlock_sample_error_bounds (θ : BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : UpperPair (2*m) → SignedCoefficient R) (x : Point (2*m)) :
    |sampledPeriodicPotential z x-periodicBlockPotential θ x| ≤ (R+1)/2 ∧
    ‖gradient (sampledPeriodicPotential z) x-gradient (periodicBlockPotential θ) x‖ ≤
      (R+1)/Real.sqrt ((2*m:ℕ):ℝ) ∧
    ‖hessian (sampledPeriodicPotential z) x-hessian (periodicBlockPotential θ) x‖ ≤
      (R+1)/((2*m:ℕ):ℝ) := by
  have hh := periodicBlockNoise_bounds θ hm R hR z x
  refine ⟨hh.1, ?_, ?_⟩
  · simpa only [periodicBlockNoise_gradient] using hh.2.1
  · simpa only [periodicBlockNoise_hessian] using hh.2.2.1

theorem periodicBlock_sample_C21 (θ : BalancedVector m) (hm : 0 < m) (R : ℝ) (hR : 2 ≤ R)
    (z : UpperPair (2*m) → SignedCoefficient R) :
    ContDiff ℝ 2 (sampledPeriodicPotential z) ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y, ‖hessian (sampledPeriodicPotential z) y-hessian (sampledPeriodicPotential z) x‖ ≤ C*‖y-x‖ := by
  refine ⟨sampledPeriodicPotential_contDiff z 2, 2*(R+1)/((2*m:ℕ):ℝ)+8/((2*m:ℕ):ℝ),
    by positivity, ?_⟩
  intro x y
  have he : hessian (sampledPeriodicPotential z) y-hessian (sampledPeriodicPotential z) x =
      (hessian (periodicBlockNoise θ z) y-hessian (periodicBlockNoise θ z) x)+
      (hessian (periodicBlockPotential θ) y-hessian (periodicBlockPotential θ) x) := by
    rw [periodicBlockNoise_hessian, periodicBlockNoise_hessian]
    abel
  rw [he, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (periodicBlockNoise_hessian_lipschitz θ hm R hR z x y)
    (periodicBlockPotential_hessian_lipschitz θ hm x y))

section Measurable
variable {d : ℕ} {R : ℝ}

private theorem measurable_countable_first {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [Countable A] [MeasurableSingletonClass A]
    (f : A → B → C) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun w : A × B => f w.1 w.2) := by
  have hh : Measurable (fun w : B × A => f w.2 w.1) := measurable_from_prod_countable hf
  exact hh.comp measurable_swap

theorem sampledPeriodicPotential_value_measurable :
    Measurable (fun w : (UpperPair d → SignedCoefficient R) × Point d => sampledPeriodicPotential w.1 w.2) := by
  apply measurable_countable_first (fun z : UpperPair d → SignedCoefficient R => sampledPeriodicPotential z)
  intro z
  exact (sampledPeriodicPotential_contDiff z 0).continuous.measurable

theorem sampledPeriodicPotential_gradient_measurable :
    Measurable (fun w : (UpperPair d → SignedCoefficient R) × Point d => gradient (sampledPeriodicPotential w.1) w.2) := by
  apply measurable_countable_first (fun z : UpperPair d → SignedCoefficient R => gradient (sampledPeriodicPotential z))
  intro z
  have hc : Continuous (gradient (sampledPeriodicPotential z)) :=
    (contDiff_gradient_one (sampledPeriodicPotential_contDiff z 2)).continuous
  exact hc.measurable

theorem sampledPeriodicPotential_hessian_measurable :
    Measurable (fun w : (UpperPair d → SignedCoefficient R) × Point d => hessian (sampledPeriodicPotential w.1) w.2) := by
  apply measurable_countable_first (fun z : UpperPair d → SignedCoefficient R => hessian (sampledPeriodicPotential z))
  intro z
  have hc : Continuous (hessian (sampledPeriodicPotential z)) :=
    continuous_hessian (sampledPeriodicPotential_contDiff z 2)
  exact hc.measurable

end Measurable
end
end SecondOrder
