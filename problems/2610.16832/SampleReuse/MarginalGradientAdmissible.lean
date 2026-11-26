import SampleReuse.MarginalGradientGeometry
import SecondOrder.RandomPeriodic

open SecondOrder MeasureTheory
open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

variable {d : ℕ}

theorem marginal_sample_mean {ε R : ℝ} (hR : 2 ≤ R) (v : Point d) (θ : Bool) (x : Point d) :
    (∫ z, marginalLoss ε v (2*ε*z.1) x
      ∂(coefficientPMF R (signValue θ) hR (signValue_sq θ)).toMeasure) =
      marginalLoss ε v (2*ε*signValue θ) x := by
  unfold marginalLoss
  rw [integral_add (integrable_const _) (Integrable.of_finite),integral_const,
    measureReal_univ_eq_one,one_smul]
  have he (z : SignedCoefficient R) : 2*ε*z.1*⟪v,x⟫_ℝ = (2*ε*⟪v,x⟫_ℝ)*z.1 := by ring
  simp_rw [he]
  rw [integral_const_mul,coefficientPMF_mean]
  ring

theorem marginal_sample_admissible (P : Parameters) {ε R : ℝ} (hε : 0 < ε) (hR : 2 ≤ R)
    {v : Point d} (hv : ‖v‖=1) (θ : Bool)
    (hgap : 4*ε ≤ P.gap) (hL₁ : 4*ε ≤ P.gradientLip) (hL₂ : 12*ε ≤ P.hessianLip)
    (hnoise : 2*ε*(R+1) ≤ P.gradientNoise) (hG : 6*ε ≤ P.gradientBound) :
    Admissible (coefficientPMF R (signValue θ) hR (signValue_sq θ)).toMeasure P
      (marginalLoss ε v (2*ε*signValue θ))
      (fun z : SignedCoefficient R => marginalLoss ε v (2*ε*z.1)) 0 := by
  have hθ : |signValue θ|=1 := by cases θ <;> norm_num [signValue]
  have hθ' : |2*ε*signValue θ|=2*ε := by rw [abs_mul,hθ,mul_one,abs_of_pos (by positivity)]
  apply finite_admissible_of_uniform_bounds _ P _ _ 0
    (fun _ => marginalLoss_contDiff ε v _ 2) (marginal_sample_mean hR v θ)
  · intro x
    exact (marginalLoss_initial_gap hε.le hv hθ'.le x).trans hgap
  · intro z x y
    exact (marginalLoss_gradient_lipschitz hε.le v _ x y).trans
      (mul_le_mul_of_nonneg_right hL₁ (norm_nonneg _))
  · intro z x y
    exact (marginalLoss_hessian_lipschitz hε.le v _ x y).trans
      (mul_le_mul_of_nonneg_right hL₂ (norm_nonneg _))
  · intro z x
    rw [marginalLoss_gradient_error ε hv,← mul_sub,abs_mul,abs_of_pos (by positivity : 0<2*ε)]
    have hh := abs_sub z.1 (signValue θ)
    rw [signedCoefficient_abs R (by linarith) z,hθ] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans hnoise
  · intro z x
    rw [marginalLoss_hessian,marginalLoss_hessian,sub_self,norm_zero]
    exact P.hessianNoise_pos.le
  · intro x
    have hh := marginalLoss_gradient_bound hε.le hv (2*ε*signValue θ) x
    rw [hθ'] at hh
    linarith

def marginalRadius (P : Parameters) (ε : ℝ) : ℝ := P.gradientNoise/(4*ε)

/-- An explicit positive threshold verifies every model bound for the exact
two-point sample law with physical support plus/minus sigma_g/2. -/
theorem marginal_calibration (P : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      2 ≤ marginalRadius P ε ∧
      4*ε ≤ P.gap ∧ 4*ε ≤ P.gradientLip ∧ 12*ε ≤ P.hessianLip ∧
      2*ε*(marginalRadius P ε+1) ≤ P.gradientNoise ∧ 6*ε ≤ P.gradientBound := by
  let η := min (P.gap/4) (min (P.gradientLip/4)
    (min (P.hessianLip/12) (min (P.gradientNoise/8) (P.gradientBound/6))))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (div_pos P.gap_pos (by norm_num)) (lt_min (div_pos P.gradientLip_pos (by norm_num))
      (lt_min (div_pos P.hessianLip_pos (by norm_num)) (lt_min
        (div_pos P.gradientNoise_pos (by norm_num)) (div_pos P.gradientBound_pos (by norm_num)))))
  refine ⟨η,hη,fun ε hε he => ?_⟩
  have hh : ε ≤ P.gap/4 ∧ ε ≤ P.gradientLip/4 ∧ ε ≤ P.hessianLip/12 ∧
      ε ≤ P.gradientNoise/8 ∧ ε ≤ P.gradientBound/6 := by
    simpa only [η,le_min_iff] using he
  have hr : 2 ≤ marginalRadius P ε := (le_div_iff₀ (by positivity : 0<4*ε)).mpr (by linarith [hh.2.2.2.1])
  refine ⟨hr,by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],?_,by linarith [hh.2.2.2.2]⟩
  have hx : 2*ε*marginalRadius P ε = P.gradientNoise/2 := by
    unfold marginalRadius
    field_simp
    ring
  nlinarith [hh.2.2.2.1]

end
end SampleReuse
