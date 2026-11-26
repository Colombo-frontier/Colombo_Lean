import SecondOrder.CurvatureRandomLoss

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

theorem curvaturePayloadScale_bounds (j : ℕ) :
    0 ≤ curvaturePayloadScale j ∧ curvaturePayloadScale j ≤ 2 := by
  unfold curvaturePayloadScale
  split_ifs <;> norm_num

theorem curvatureNoisePayload_bounds (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (R : ℝ) (hR : 2 ≤ R) (z : CurvatureCoefficients m T R) (j : ℕ) (x : CurvatureSpace m T) :
    |curvatureNoisePayload Θ z j x| ≤ R+1 ∧
    ‖gradient (curvatureNoisePayload Θ z j) x‖ ≤ 2*(R+1)/Real.sqrt ((2*m:ℕ):ℝ) ∧
    ‖fderiv ℝ (gradient (curvatureNoisePayload Θ z j)) x‖ ≤ 2*(R+1)/((2*m:ℕ):ℝ) := by
  letI : NormedSpace ℝ (CurvatureSpace m T) := inferInstance
  by_cases hj : j<T+1
  · let i : Fin (T+1) := ⟨j,hj⟩
    let f : CurvatureSpace m T → ℝ := periodicBlockNoise (Θ i) (z i) ∘ blockProj i
    have hf : ContDiff ℝ 2 f := (periodicBlockNoise_contDiff (Θ i) (z i) 2).comp
      (blockProj (E := Point (2*m)) i).contDiff
    have he : curvatureNoisePayload Θ z j = fun y => curvaturePayloadScale j*f y := by
      funext y
      simp only [curvatureNoisePayload, dif_pos hj]
      rfl
    have hs := curvaturePayloadScale_bounds j
    have hn := periodicBlockNoise_bounds (Θ i) hm R hR (z i) (x i)
    have hg : ‖gradient f x‖ ≤ (R+1)/Real.sqrt ((2*m:ℕ):ℝ) :=
      (gradient_linear_contraction _ (periodicBlockNoise_contDiff (Θ i) (z i) 2)
        (blockProj i) (blockProj_norm_le_one i) x).trans hn.2.1
    have hH : ‖fderiv ℝ (gradient f) x‖ ≤ (R+1)/((2*m:ℕ):ℝ) :=
      (hessian_linear_contraction _ (periodicBlockNoise_contDiff (Θ i) (z i) 2)
        (blockProj i) (blockProj_norm_le_one i) x).trans hn.2.2.1
    rw [he]
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg hs.1]
      have hh := mul_le_mul hs.2 hn.1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
      change curvaturePayloadScale j*|f x| ≤ R+1
      change curvaturePayloadScale j*|f x| ≤ 2*((R+1)/2) at hh
      linarith
    · rw [gradient_const_mul_scalar (hf.differentiable (by norm_num)), norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact (mul_le_mul hs.2 hg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
    · rw [hessian_const_mul_scalar hf, norm_smul (curvaturePayloadScale j) (fderiv ℝ (gradient f) x),
        Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact (mul_le_mul hs.2 hH (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  · have he : curvatureNoisePayload Θ z j = fun _ => (0:ℝ) := by
      funext y
      simp only [curvatureNoisePayload, dif_neg hj]
    rw [he]
    simp only [gradient, fderiv_const, map_zero, Pi.zero_apply, norm_zero, abs_zero]
    constructor
    · linarith
    constructor
    · positivity
    · have hg : gradient (fun _ : CurvatureSpace m T => (0:ℝ)) = fun _ => 0 := by
        funext y
        simp only [gradient, fderiv_const, Pi.zero_apply, map_zero]
      rw [hg, fderiv_const]
      simp only [Pi.zero_apply, norm_zero]
      positivity

end
end SecondOrder
