import SampleReuse.MarginalGradientGeometry

open SecondOrder GradientHessian.LocalizedNormDerivatives
open GradientHessian.SmoothNormCompression
open scoped InnerProductSpace
namespace SampleReuse
noncomputable section
variable {d : ℕ}

theorem unitCompressionDerivative_nonneg (x w : Point d) :
    0 ≤ ⟪unitCompressionDerivative x w, w⟫_ℝ := by
  have hp := compressionFactor_pos x
  have hi := compressionFactor_identity x
  have hc := abs_real_inner_le_norm x w
  have hsq : ⟪x,w⟫_ℝ ^ 2 ≤ ‖x‖^2*‖w‖^2 := by
    nlinarith only [sq_nonneg (|⟪x,w⟫_ℝ| + ‖x‖*‖w‖), sq_abs ⟪x,w⟫_ℝ,
      mul_nonneg (sub_nonneg.mpr hc) (add_nonneg (abs_nonneg ⟪x,w⟫_ℝ)
        (mul_nonneg (norm_nonneg x) (norm_nonneg w)))]
  have hm := mul_le_mul_of_nonneg_left hsq (pow_nonneg hp.le 3)
  have he : compressionFactor x ^ 3 * (‖x‖^2*‖w‖^2) =
      compressionFactor x*‖w‖^2-compressionFactor x^3*‖w‖^2 := by
    have hh := congrArg (fun t => compressionFactor x*‖w‖^2*t) hi
    dsimp only at hh
    nlinarith only [hh]
  rw [he] at hm
  simp only [unitCompressionDerivative_apply,inner_sub_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  nlinarith only [hm,mul_nonneg (pow_nonneg hp.le 3) (sq_nonneg ‖w‖)]

theorem marginalLoss_hessian_nonneg {ε : ℝ} (hε : 0 ≤ ε)
    (v : Point d) (z : ℝ) (x w : Point d) :
    0 ≤ ⟪hessian (marginalLoss ε v z) x w,w⟫_ℝ := by
  rw [marginalLoss_hessian,ContinuousLinearMap.smul_apply,real_inner_smul_left]
  exact mul_nonneg (by positivity) (unitCompressionDerivative_nonneg x w)

theorem marginalLoss_isSOSP_iff {ε γ η : ℝ} (hε : 0 ≤ ε) (hγ : 0 ≤ γ)
    (v : Point d) (z : ℝ) (x : Point d) :
    IsSOSP (marginalLoss ε v z) η γ x ↔ ‖gradient (marginalLoss ε v z) x‖ ≤ η := by
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx,fun w => ?_⟩
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) (sq_nonneg ‖w‖)).trans
      (marginalLoss_hessian_nonneg hε v z x w)

theorem marginalLoss_minimum_lower {ε : ℝ} (hε : 0 ≤ ε) {v : Point d} (hv : ‖v‖ = 1)
    (θ : Bool) (x : Point d) : 2*Real.sqrt 3*ε ≤ marginalLoss ε v (2*ε*signValue θ) x := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hq := Real.sq_sqrt (show 0 ≤ 1+‖x‖^2 by positivity)
  have hc := real_inner_mul_inner_self_le v x
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hv,one_pow,one_mul] at hc
  have hθ := signValue_sq θ
  let t := signValue θ*⟪v,x⟫_ℝ
  have ht : t^2 ≤ ‖x‖^2 := by
    dsimp only [t]
    nlinarith only [hc,hθ,sq_nonneg ⟪v,x⟫_ℝ]
  have hroot : Real.sqrt 3 ≤ 2*Real.sqrt (1+‖x‖^2)+t := by
    nlinarith only [hs,hq,ht,Real.sqrt_nonneg 3,Real.sqrt_nonneg (1+‖x‖^2),
      sq_nonneg (Real.sqrt 3*t+1)]
  have hm := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*ε by positivity)
  unfold marginalLoss unitSmoothNorm
  dsimp only [t] at hm
  nlinarith only [hm]

theorem marginalLoss_at_minimizer (ε : ℝ) {v : Point d} (hv : ‖v‖ = 1) (θ : Bool) :
    marginalLoss ε v (2*ε*signValue θ) ((-signValue θ/Real.sqrt 3) • v) = 2*Real.sqrt 3*ε := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hn : ‖(-signValue θ/Real.sqrt 3) • v‖^2 = 1/3 := by
    rw [norm_smul,hv,mul_one,Real.norm_eq_abs,sq_abs,div_pow,neg_sq,signValue_sq,hs]
  have hr : Real.sqrt (1+1/3) = 2/Real.sqrt 3 := by
    apply (eq_div_iff hp.ne').mpr
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 1+1/3 by norm_num)]
    norm_num
  unfold marginalLoss unitSmoothNorm
  rw [hn,hr,inner_smul_right,real_inner_self_eq_norm_sq,hv,one_pow,mul_one]
  have hθ := signValue_sq θ
  field_simp
  linear_combination -2*ε*hθ -2*ε*hs

/-- Exact appendix gap, including attainment; in dimension one this is the
manuscript's displayed (4 - 2 sqrt 3) epsilon. -/
theorem marginalLoss_exact_gap {ε : ℝ} (hε : 0 ≤ ε) {v : Point d} (hv : ‖v‖ = 1) (θ : Bool) :
    IsLeast (Set.range (marginalLoss ε v (2*ε*signValue θ))) (2*Real.sqrt 3*ε) ∧
      marginalLoss ε v (2*ε*signValue θ) 0-2*Real.sqrt 3*ε = (4-2*Real.sqrt 3)*ε := by
  refine ⟨⟨⟨(-signValue θ/Real.sqrt 3) • v,marginalLoss_at_minimizer ε hv θ⟩,?_⟩,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact marginalLoss_minimum_lower hε hv θ x
  · simp [marginalLoss,unitSmoothNorm]
    ring

end
end SampleReuse
