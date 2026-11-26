import SecondOrder.FirstOrderPayloadBounds

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderNoiseConstant : ℝ := 441296

theorem firstOrderNoiseConstant_pos : 0<firstOrderNoiseConstant := by norm_num [firstOrderNoiseConstant]

/-- Differentiating the complete selector does not introduce a chain-length factor. -/
theorem firstOrderChainNoise_bounds (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) (x : FirstOrderSpace d T) :
    |firstOrderChainNoise Θ z x|≤firstOrderNoiseConstant*(R+1) ∧
    ‖gradient (firstOrderChainNoise Θ z) x‖≤firstOrderNoiseConstant*(R+1) ∧
    ‖fderiv ℝ (gradient (firstOrderChainNoise Θ z)) x‖≤firstOrderNoiseConstant*(R+1) := by
  have hA : 0≤R+1 := by linarith
  have hn := reverseSelector_bounds (fun i => firstOrderBlockCompletion (Θ i)) (firstOrderNoisePayload Θ z)
    (fun i => (firstOrderBlockCompletion_contDiff (Θ i)).of_le (show (2:WithTop ℕ∞)≤3 by decide))
    (fun j _ => firstOrderNoisePayload_contDiff Θ z j 2) x
    (fun i => (firstOrderBlockCompletion_mem (Θ i) (x i)).1)
    (fun i => (firstOrderBlockCompletion_mem (Θ i) (x i)).2)
    (8*(R+1)) (8*(R+1)) (16*(R+1)) 140 7840
    (by positivity) (by positivity) (by positivity) (by norm_num) (by norm_num)
    (fun j _ => (firstOrderNoisePayload_bounds Θ hd R hR z j x).1)
    (fun j _ => (firstOrderNoisePayload_bounds Θ hd R hR z j x).2.1)
    (fun j _ => (firstOrderNoisePayload_bounds Θ hd R hR z j x).2.2)
    (fun i => by convert firstOrderBlockCompletion_fisher (Θ i) hd (x i) using 1 <;> norm_num)
    (fun i => firstOrderBlockCompletion_hessian_bound (Θ i) hd (x i))
  change ContDiff ℝ 2 (firstOrderChainNoise Θ z) ∧ _ at hn
  unfold firstOrderNoiseConstant
  refine ⟨?_,?_,?_⟩
  · exact hn.2.1.trans (by linarith)
  · exact hn.2.2.1.trans (by linarith)
  · exact hn.2.2.2.trans_eq (by ring)

theorem firstOrderRandomLoss_error_bounds (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) (x : FirstOrderSpace d T) :
    |firstOrderRandomLoss Θ z x-firstOrderChain Θ x|≤firstOrderNoiseConstant*(R+1) ∧
    ‖gradient (firstOrderRandomLoss Θ z) x-gradient (firstOrderChain Θ) x‖≤firstOrderNoiseConstant*(R+1) ∧
    ‖fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) x-fderiv ℝ (gradient (firstOrderChain Θ)) x‖≤
      firstOrderNoiseConstant*(R+1) := by
  have hf := (firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hg := (firstOrderChainNoise_contDiff Θ z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have he : firstOrderRandomLoss Θ z=fun y => firstOrderChain Θ y+firstOrderChainNoise Θ z y := rfl
  rw [he,hessian_add_scalar hf hg,
    gradient_add_scalar (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  simpa only [add_sub_cancel_left] using firstOrderChainNoise_bounds Θ hd R hR z x

end
end SecondOrder
