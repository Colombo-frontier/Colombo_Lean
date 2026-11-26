import SampleReuse.ReverseStickThirdLocalization
import SampleReuse.SlowSampleGate
import SecondOrder.FirstOrderSampleRegularity

/-! Concrete payload and chain-length-independent sampled noise third derivatives. -/

open SecondOrder
namespace SampleReuse
noncomputable section
variable {d T : ℕ}

theorem firstOrderNoisePayload_third_bound (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) (R : ℝ) (hR : 2 ≤ R) (z : FirstOrderCoefficients d T R)
    (j : ℕ) (x : FirstOrderSpace d T) :
    ‖iteratedFDeriv ℝ 3 (firstOrderNoisePayload Θ z j) x‖ ≤ 48 * (R + 1) * Real.sqrt d := by
  by_cases hj : j < T + 1
  · let i : Fin (T + 1) := ⟨j, hj⟩
    let f : FirstOrderSpace d T → ℝ := firstOrderBlockNoise (Θ i) (z i) ∘ blockProj i
    have hf : ContDiff ℝ 3 f := (firstOrderBlockNoise_contDiff (Θ i) (z i) 3).comp
      (blockProj (E := Point d) i).contDiff
    have he : firstOrderNoisePayload Θ z j = fun y => firstOrderPayloadScale j • f y := by
      funext y
      simp only [firstOrderNoisePayload, dif_pos hj, smul_eq_mul]
      rfl
    have hs := firstOrderPayloadScale_bounds j
    have hn := (firstOrderBlockNoise_bounds (Θ i) hd R hR (z i) (x i)).2.2.2
    have hder : ‖iteratedFDeriv ℝ 3 f x‖ ≤ 24 * (R + 1) * Real.sqrt d :=
      (iteratedFDeriv_linear_contraction (firstOrderBlockNoise (Θ i) (z i))
        (blockProj (E := Point d) i) (blockProj_norm_le_one i) 3
        (firstOrderBlockNoise_contDiff (Θ i) (z i) 3) x).trans hn
    rw [he, iteratedFDeriv_const_smul_apply' hf.contDiffAt,
      norm_smul (firstOrderPayloadScale j) (iteratedFDeriv ℝ 3 f x),
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul hs.2 hder (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · have he : firstOrderNoisePayload Θ z j = fun _ => (0 : ℝ) := by
      funext y
      simp only [firstOrderNoisePayload, dif_neg hj]
    rw [he, iteratedFDeriv_const_of_ne (by decide : (3 : ℕ) ≠ 0)]
    simp only [Pi.zero_apply, norm_zero]
    positivity

def sampleNoiseThirdConstant : ℝ := thirdMixtureBound 8 8 16 48 140 10000 firstOrderJetConstant

theorem sampleNoiseThirdConstant_pos : 0 < sampleNoiseThirdConstant := by
  norm_num [sampleNoiseThirdConstant, thirdMixtureBound, firstOrderJetConstant, completionDerivativeBound]

/-- Unlike the predecessor's existential BoundedC3 witness, this bound is
explicit and has no dependence on T. Its sqrt(d) factor is removed by the
manuscript's slow dilation after amplitude scaling. -/
theorem firstOrderChainNoise_third_uniform (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) (R : ℝ) (hR : 2 ≤ R) (z : FirstOrderCoefficients d T R)
    (x : FirstOrderSpace d T) :
    ‖iteratedFDeriv ℝ 3 (firstOrderChainNoise Θ z) x‖ ≤
      sampleNoiseThirdConstant * (R + 1) * Real.sqrt d := by
  have hJ : 0 ≤ firstOrderJetConstant := le_trans (by norm_num) firstOrderJetConstant_ge_one
  have hRp : 0 ≤ R + 1 := by linarith
  have hs : 1 ≤ Real.sqrt (d : ℝ) := by
    apply (Real.one_le_sqrt).2
    exact_mod_cast hd
  have hh := reverseBlockSelector_third_bound
    (fun i => firstOrderBlockCompletion (Θ i)) (firstOrderNoisePayload Θ z)
    (fun i => firstOrderBlockCompletion_contDiff (Θ i))
    (fun j _ => firstOrderNoisePayload_contDiff Θ z j 3) x
    (fun i => (firstOrderBlockCompletion_mem (Θ i) (x i)).1)
    (fun i => (firstOrderBlockCompletion_mem (Θ i) (x i)).2)
    (8 * (R + 1)) (8 * (R + 1)) (16 * (R + 1)) (48 * (R + 1) * Real.sqrt d)
    140 10000 (firstOrderJetConstant * Real.sqrt d)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by norm_num) (by norm_num) (by positivity)
    (fun j _ => (firstOrderNoisePayload_bounds Θ hd R hR z j x).1)
    (fun j _ => by simpa only [norm_gradient_eq_fderiv] using
      (firstOrderNoisePayload_bounds Θ hd R hR z j x).2.1)
    (fun j _ => by simpa only [norm_hessian_eq_second_fderiv] using
      (firstOrderNoisePayload_bounds Θ hd R hR z j x).2.2)
    (fun j _ => firstOrderNoisePayload_third_bound Θ hd R hR z j x)
    (fun i => by simpa only [norm_gradient_eq_fderiv,
      show (140 : ℝ) ^ 2 = 19600 by norm_num] using firstOrderBlockCompletion_fisher (Θ i) hd (x i))
    (fun i => firstOrderBlockCompletion_second_fisher (Θ i) hd (x i))
    (fun i => firstOrderBlockCompletion_third_bound (Θ i) hd (x i))
  apply hh.2.trans
  unfold thirdMixtureBound sampleNoiseThirdConstant
  unfold thirdMixtureBound
  have hm := mul_le_mul_of_nonneg_left hs hRp
  nlinarith

end
end SampleReuse
