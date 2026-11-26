import SecondOrder.CurvaturePayloadBounds

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

theorem periodicCompletion_fisher_coarse (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicCompletion θ) x‖^2 ≤
      (completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ))^2 *
        periodicCompletion θ x*(1-periodicCompletion θ x) := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hb := periodicCompletion_mem θ x
  have hc : 1225*(64/3:ℝ)^2 ≤ completionDerivativeBound^2 := by norm_num [completionDerivativeBound]
  exact (periodicCompletion_fisher θ x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)) hb.1) (sub_nonneg.mpr hb.2))

def curvatureNoiseConstant : ℝ := 2+6*completionDerivativeBound+2*completionDerivativeBound^2

theorem curvatureNoiseConstant_bounds :
    1 ≤ curvatureNoiseConstant ∧ 2+completionDerivativeBound ≤ curvatureNoiseConstant := by
  norm_num [curvatureNoiseConstant, completionDerivativeBound]

/-- All realized full-chain errors have the manuscript's dimension scaling,
with one universal constant independent of chain length. -/
theorem curvatureChainNoise_bounds (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : CurvatureCoefficients m T R) (x : CurvatureSpace m T) :
    |curvatureChainNoise Θ z x| ≤ curvatureNoiseConstant*(R+1) ∧
    ‖gradient (curvatureChainNoise Θ z) x‖ ≤ curvatureNoiseConstant*(R+1)/Real.sqrt ((2*m:ℕ):ℝ) ∧
    ‖fderiv ℝ (gradient (curvatureChainNoise Θ z)) x‖ ≤ curvatureNoiseConstant*(R+1)/((2*m:ℕ):ℝ) := by
  have hA : 0 ≤ R+1 := by linarith
  have hD : 0 ≤ ((2*m:ℕ):ℝ) := Nat.cast_nonneg _
  have hn := reverseSelector_bounds (fun i => periodicCompletion (Θ i)) (curvatureNoisePayload Θ z)
    (fun i => (periodicCompletion_contDiff (Θ i)).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
    (fun j _ => curvatureNoisePayload_contDiff Θ z j 2) x
    (fun i => (periodicCompletion_mem (Θ i) (x i)).1)
    (fun i => (periodicCompletion_mem (Θ i) (x i)).2)
    (R+1) (2*(R+1)/Real.sqrt ((2*m:ℕ):ℝ)) (2*(R+1)/((2*m:ℕ):ℝ))
    (completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ)) (completionDerivativeBound/((2*m:ℕ):ℝ))
    hA (by positivity) (by positivity) (by unfold completionDerivativeBound; positivity)
    (by unfold completionDerivativeBound; positivity)
    (fun j _ => (curvatureNoisePayload_bounds Θ hm R hR z j x).1)
    (fun j _ => (curvatureNoisePayload_bounds Θ hm R hR z j x).2.1)
    (fun j _ => (curvatureNoisePayload_bounds Θ hm R hR z j x).2.2)
    (fun i => periodicCompletion_fisher_coarse (Θ i) (x i))
    (fun i => periodicCompletion_hessian_coarse_bound (Θ i) (x i))
  change ContDiff ℝ 2 (curvatureChainNoise Θ z) ∧ _ at hn
  refine ⟨?_, ?_, ?_⟩
  · exact hn.2.1.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right curvatureNoiseConstant_bounds.1 hA)
  · calc
      _ ≤ 2*(R+1)/Real.sqrt ((2*m:ℕ):ℝ)+(R+1)*(completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ)) := hn.2.2.1
      _ = (2+completionDerivativeBound)*(R+1)/Real.sqrt ((2*m:ℕ):ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right curvatureNoiseConstant_bounds.2 hA) (Real.sqrt_nonneg _)
  · have hs : (2*(R+1)/Real.sqrt ((2*m:ℕ):ℝ)) * (completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ)) =
        2*(R+1)*completionDerivativeBound/((2*m:ℕ):ℝ) := by
      rw [div_mul_div_comm, Real.mul_self_sqrt hD]
    have he : 2*(R+1)/((2*m:ℕ):ℝ) +
        2*(2*(R+1)/Real.sqrt ((2*m:ℕ):ℝ))*(completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ)) +
        2*(R+1)*(completionDerivativeBound/((2*m:ℕ):ℝ)+(completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ))^2) =
          curvatureNoiseConstant*(R+1)/((2*m:ℕ):ℝ) := by
      rw [mul_assoc 2, hs, div_pow, Real.sq_sqrt hD]
      unfold curvatureNoiseConstant
      ring
    exact hn.2.2.2.trans_eq he

theorem curvatureRandomLoss_error_bounds (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : CurvatureCoefficients m T R) (x : CurvatureSpace m T) :
    |curvatureRandomLoss Θ z x-curvatureChain Θ x| ≤ curvatureNoiseConstant*(R+1) ∧
    ‖gradient (curvatureRandomLoss Θ z) x-gradient (curvatureChain Θ) x‖ ≤
      curvatureNoiseConstant*(R+1)/Real.sqrt ((2*m:ℕ):ℝ) ∧
    ‖fderiv ℝ (gradient (curvatureRandomLoss Θ z)) x-fderiv ℝ (gradient (curvatureChain Θ)) x‖ ≤
      curvatureNoiseConstant*(R+1)/((2*m:ℕ):ℝ) := by
  have hf := (curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)
  have hg := (curvatureChainNoise_contDiff Θ z).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)
  have he : curvatureRandomLoss Θ z = fun y => curvatureChain Θ y+curvatureChainNoise Θ z y := rfl
  rw [he, hessian_add_scalar hf hg,
    gradient_add_scalar (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  simpa only [add_sub_cancel_left] using curvatureChainNoise_bounds Θ hm R hR z x

end
end SecondOrder
