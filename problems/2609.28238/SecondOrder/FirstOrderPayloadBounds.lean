import SecondOrder.FirstOrderRandomLoss

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

theorem firstOrderPayloadScale_bounds (j : ℕ) :
    0≤firstOrderPayloadScale j ∧ firstOrderPayloadScale j≤2 := by
  unfold firstOrderPayloadScale
  split_ifs <;> norm_num

theorem firstOrderNoisePayload_bounds (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (R : ℝ) (hR : 2≤R) (z : FirstOrderCoefficients d T R) (j : ℕ) (x : FirstOrderSpace d T) :
    |firstOrderNoisePayload Θ z j x|≤8*(R+1) ∧
    ‖gradient (firstOrderNoisePayload Θ z j) x‖≤8*(R+1) ∧
    ‖fderiv ℝ (gradient (firstOrderNoisePayload Θ z j)) x‖≤16*(R+1) := by
  letI : NormedSpace ℝ (FirstOrderSpace d T) := inferInstance
  by_cases hj : j<T+1
  · let i : Fin (T+1) := ⟨j,hj⟩
    let f : FirstOrderSpace d T → ℝ := firstOrderBlockNoise (Θ i) (z i) ∘ blockProj i
    have hf : ContDiff ℝ 2 f := (firstOrderBlockNoise_contDiff (Θ i) (z i) 2).comp
      (blockProj (E := Point d) i).contDiff
    have he : firstOrderNoisePayload Θ z j=fun y => firstOrderPayloadScale j*f y := by
      funext y
      simp only [firstOrderNoisePayload,dif_pos hj]
      rfl
    have hs := firstOrderPayloadScale_bounds j
    have hn := firstOrderBlockNoise_bounds (Θ i) hd R hR (z i) (x i)
    have hg : ‖gradient f x‖≤4*(R+1) :=
      (gradient_linear_contraction _ (firstOrderBlockNoise_contDiff (Θ i) (z i) 2)
        (blockProj i) (blockProj_norm_le_one i) x).trans hn.2.1
    have hH : ‖fderiv ℝ (gradient f) x‖≤8*(R+1) :=
      (hessian_linear_contraction _ (firstOrderBlockNoise_contDiff (Θ i) (z i) 2)
        (blockProj i) (blockProj_norm_le_one i) x).trans hn.2.2.1
    rw [he]
    refine ⟨?_,?_,?_⟩
    · rw [abs_mul,abs_of_nonneg hs.1]
      exact (mul_le_mul hs.2 hn.1 (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
    · rw [gradient_const_mul_scalar (hf.differentiable (by norm_num)),norm_smul,
        Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_mul hs.2 hg (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
    · rw [hessian_const_mul_scalar hf,norm_smul (firstOrderPayloadScale j) (fderiv ℝ (gradient f) x),
        Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_mul hs.2 hH (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  · have he : firstOrderNoisePayload Θ z j=fun _ => (0:ℝ) := by
      funext y
      simp only [firstOrderNoisePayload,dif_neg hj]
    rw [he]
    simp only [gradient,fderiv_const,map_zero,Pi.zero_apply,norm_zero,abs_zero]
    constructor
    · linarith
    constructor
    · linarith
    · have hg : gradient (fun _ : FirstOrderSpace d T => (0:ℝ))=fun _ => 0 := by
        funext y
        simp only [gradient,fderiv_const,Pi.zero_apply,map_zero]
      rw [hg,fderiv_const]
      simp only [Pi.zero_apply,norm_zero]
      linarith

end
end SecondOrder
