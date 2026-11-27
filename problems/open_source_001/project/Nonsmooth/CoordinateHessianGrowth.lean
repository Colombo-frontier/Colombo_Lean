import Nonsmooth.VectorScoreCovarianceBound

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
local instance coordinateGrowthDualNormedGroup {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance coordinateGrowthDualNormedSpace {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance


theorem vector_linear_score_square_growth {E G : Type} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (t : E) (s : ℝ → G) {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ x, ‖s x‖ ≤ C * (1 + ‖t‖ + |x|)) (x : ℝ) :
    ‖s x‖ ^ 2 ≤ 3 * C ^ 2 * (1 + ‖t‖ ^ 2 + x ^ 2) := by
  have hb := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C * (1 + ‖t‖ + |x|))).mpr (hs x)
  rw [mul_pow] at hb
  have hp : (1 + ‖t‖ + |x|) ^ 2 ≤ 3 * (1 + ‖t‖ ^ 2 + x ^ 2) := by
    nlinarith [sq_nonneg (‖t‖ - 1), sq_nonneg (|x| - 1), sq_nonneg (‖t‖ - |x|), sq_abs x]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg C)
  nlinarith

theorem coordinate_hessian_norm_of_second_moment {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : E)
    (s : ℝ → E →L[ℝ] ℝ) (H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hs : MemLp s 2 μ) (hH : Integrable H μ) (hx : MemLp (fun x : ℝ => x) 2 μ)
    {C D : ℝ} (hC : 0 ≤ C)
    (hsb : ∀ x, ‖s x‖ ≤ C * (1 + ‖t‖ + |x|))
    (hHb : ∀ x, ‖H x‖ ≤ D * (1 + ‖t‖ ^ 2 + x ^ 2)) :
    ‖(∫ x, H x - (s x).smulRight (s x) ∂μ) +
      (∫ x, s x ∂μ).smulRight (∫ x, s x ∂μ)‖ ≤
        (D + 6 * C ^ 2) * (1 + ‖t‖ ^ 2 + ∫ x : ℝ, x ^ 2 ∂μ) := by
  have hq : Integrable (fun x : ℝ => 1 + ‖t‖ ^ 2 + x ^ 2) μ :=
    (integrable_const (1 + ‖t‖ ^ 2)).add hx.integrable_sq
  have hHn : Integrable (fun x => ‖H x‖) μ := Integrable.norm (f := H) hH
  have hmean : (∫ x : ℝ, 1 + ‖t‖ ^ 2 + x ^ 2 ∂μ) = 1 + ‖t‖ ^ 2 + ∫ x : ℝ, x ^ 2 ∂μ := by
    rw [integral_add (integrable_const (1 + ‖t‖ ^ 2)) hx.integrable_sq, integral_const]
    simp only [probReal_univ, one_smul]
  have h1 : (∫ x, ‖H x‖ ∂μ) ≤ D * (1 + ‖t‖ ^ 2 + ∫ x : ℝ, x ^ 2 ∂μ) := by
    rw [← hmean, ← integral_const_mul]
    exact integral_mono hHn (hq.const_mul D) hHb
  have h2 : (∫ x, ‖s x‖ ^ 2 ∂μ) ≤ (3 * C ^ 2) * (1 + ‖t‖ ^ 2 + ∫ x : ℝ, x ^ 2 ∂μ) := by
    rw [← hmean, ← integral_const_mul]
    exact integral_mono hs.norm.integrable_sq (hq.const_mul (3 * C ^ 2))
      (vector_linear_score_square_growth t s hC hsb)
  have h := score_covariance_hessian_norm_bound μ s H hs hH
  nlinarith

theorem coordinate_hessian_polynomial_growth {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : E)
    (s : ℝ → E →L[ℝ] ℝ) (H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hs : MemLp s 2 μ) (hH : Integrable H μ) (hx : MemLp (fun x : ℝ => x) 2 μ)
    {C D K : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsb : ∀ x, ‖s x‖ ≤ C * (1 + ‖t‖ + |x|))
    (hHb : ∀ x, ‖H x‖ ≤ D * (1 + ‖t‖ ^ 2 + x ^ 2))
    (hm : (∫ x : ℝ, x ^ 2 ∂μ) ≤ K * (1 + ‖t‖ ^ 2)) :
    ‖(∫ x, H x - (s x).smulRight (s x) ∂μ) +
      (∫ x, s x ∂μ).smulRight (∫ x, s x ∂μ)‖ ≤
        ((D + 6 * C ^ 2) * (1 + K)) * (1 + ‖t‖ ^ 2) := by
  have h := coordinate_hessian_norm_of_second_moment μ t s H hs hH hx hC hsb hHb
  have hb := mul_le_mul_of_nonneg_left hm (show 0 ≤ D + 6 * C ^ 2 by positivity)
  nlinarith

end
end Nonsmooth
