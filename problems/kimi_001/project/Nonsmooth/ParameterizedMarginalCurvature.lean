import Nonsmooth.RegularStrongSliceFamily

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem hessian_determinant_with_margin {a b c ρ θ : ℝ} (hθ : θ < ρ)
    (h : ∀ p q : ℝ, ρ * (p ^ 2 + q ^ 2) ≤ a * p ^ 2 + 2 * b * p * q + c * q ^ 2) :
    0 < a - θ ∧ b ^ 2 ≤ (a - θ) * (c - θ) := by
  have ha : 0 < a - θ := by have h0 := h 1 0; norm_num at h0; linarith
  refine ⟨ha, ?_⟩
  have hpsd (p q : ℝ) : 0 ≤ (a - θ) * p ^ 2 + 2 * b * p * q + (c - θ) * q ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hθ.le) (add_nonneg (sq_nonneg p) (sq_nonneg q))
    nlinarith [h p q]
  have hp : 0 ≤ (a - θ) * ((a - θ) * (c - θ) - b ^ 2) := by
    nlinarith [hpsd b (-(a - θ))]
  by_contra hn
  have hh := mul_neg_of_pos_of_neg ha (sub_neg.mpr (lt_of_not_ge hn))
  linarith

theorem regularFamily_marginal_curvature_parameter {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) {θ : ℝ} (hθ : 0 < θ) (t : ℝ)
    (ht : ∀ x, 0 < H.dxx t x - θ)
    (hH : ∀ x, (H.mixed t x) ^ 2 ≤ (H.dxx t x - θ) * (H.gamma t x - θ)) :
    θ ≤ deriv (deriv (fun r => -Real.log (potentialPartition V r))) t := by
  let Q := realDensityLaw (fun x => Real.exp (-V t x))
  letI : IsProbabilityMeasure Q := (regularFamily_slice_probability_and_memLp H t).1
  have hquot (x : ℝ) : (H.mixed t x) ^ 2 / (H.dxx t x - θ) ≤ H.gamma t x - θ :=
    (div_le_iff₀ (ht x)).mpr (by simpa only [mul_comm] using hH x)
  have hc : Continuous (fun x => (H.mixed t x) ^ 2 / (H.dxx t x - θ)) :=
    ((H.mixed_continuous t).pow 2).div ((H.dxx_continuous t).sub continuous_const)
      (fun x => (ht x).ne')
  have hgrad : Integrable (fun x => (H.mixed t x) ^ 2 / (H.dxx t x - θ)) Q := by
    apply ((H.gamma_integrable t).sub (integrable_const θ)).mono' hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (ht x).le)]
    exact hquot x
  have hb := full_line_covariance_brascamp_lieb hθ (V t) (H.dx t) (H.dxx t)
    (H.score t) (H.mixed t) (H.dx_continuous t) (H.dxx_continuous t)
    (H.score_continuous t) (H.mixed_continuous t) (H.dx_derivative t)
    (H.dxx_derivative t) (H.mixed_derivative t) ht (H.score_memLp t) hgrad
  try dsimp only at hb
  have he := integral_mono hgrad ((H.gamma_integrable t).sub (integrable_const θ)) hquot
  simp only [Pi.sub_apply] at he
  rw [integral_sub (H.gamma_integrable t) (integrable_const θ), integral_const,
    probReal_univ, one_smul] at he
  have hd : deriv (fun r => -Real.log (potentialPartition V r)) = potentialExpectation V H.score := by
    funext r
    exact (regularFamily_marginal_derivative H r).deriv
  rw [hd, (regularFamily_marginal_score_derivative H t).deriv]
  change (θ : ℝ) ≤ (∫ x, H.gamma t x ∂Q) - variance (H.score t) Q
  have hn : 0 ≤ θ * (∫ x, x * (H.score t x - ∫ y, H.score t y ∂Q) ∂Q) ^ 2 := by positivity
  change variance (H.score t) Q + θ * (∫ x, x * (H.score t x - ∫ y, H.score t y ∂Q) ∂Q) ^ 2 ≤ _ at hb
  linarith

/-- Arbitrarily small reserved Hessian margins yield the full original
curvature constant after integrating a coordinate; no constant is lost. -/
theorem regularFamily_marginal_preserves_curvature {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (ρ : ℝ) (t : ℝ)
    (hH : ∀ x p q, ρ * (p ^ 2 + q ^ 2) ≤
      H.dxx t x * p ^ 2 + 2 * H.mixed t x * p * q + H.gamma t x * q ^ 2) :
    ρ ≤ deriv (deriv (fun r => -Real.log (potentialPartition V r))) t := by
  let c := deriv (deriv (fun r => -Real.log (potentialPartition V r))) t
  have hc : 1 ≤ c := by
    have hd : deriv (fun r => -Real.log (potentialPartition V r)) = potentialExpectation V H.score := by
      funext r
      exact (regularFamily_marginal_derivative H r).deriv
    dsimp only [c]
    rw [hd, (regularFamily_marginal_score_derivative H t).deriv]
    have hb := regularFamily_marginal_curvature_lower H t
    nlinarith [sq_nonneg (deriv (potentialExpectation V (fun _ x => x)) t)]
  by_contra hn
  have hlt : c < ρ := lt_of_not_ge hn
  let θ := (c + ρ) / 2
  have hθ0 : 0 < θ := by dsimp only [θ]; linarith
  have hθρ : θ < ρ := by dsimp only [θ]; linarith
  have hm (x : ℝ) := hessian_determinant_with_margin hθρ (hH x)
  have hb := regularFamily_marginal_curvature_parameter H hθ0 t (fun x => (hm x).1) (fun x => (hm x).2)
  change θ ≤ c at hb
  dsimp only [θ] at hb
  linarith

end
end Nonsmooth
