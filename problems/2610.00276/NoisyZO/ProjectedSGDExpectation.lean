import NoisyZO.ProjectedSGDStep
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Expected projected-SGD step

This module integrates the pointwise projection inequality.  The bias is imposed
on the mean stochastic gradient, while the random fluctuation enters only
through its second moment, matching the stochastic recurrence in the manuscript.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace NoisyZO

/-- Projection algebra before inserting a bias bound. -/
theorem projected_gradient_step_raw
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x xstar xnext g : E) (η : ℝ) (hη : 0 ≤ η)
    (hprojection : ‖xnext - xstar‖ ≤ ‖(x - η • g) - xstar‖) :
    ‖xnext - xstar‖ ^ 2 ≤
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪g, x - xstar⟫_ℝ + η ^ 2 * ‖g‖ ^ 2 := by
  have hproj_sq :
      ‖xnext - xstar‖ ^ 2 ≤ ‖(x - η • g) - xstar‖ ^ 2 := by
    nlinarith [norm_nonneg (xnext - xstar), norm_nonneg ((x - η • g) - xstar)]
  have hrewrite : (x - η • g) - xstar = (x - xstar) - η • g := by abel
  have hinner_smul : ⟪x - xstar, η • g⟫_ℝ = η * ⟪g, x - xstar⟫_ℝ := by
    rw [real_inner_smul_right, real_inner_comm]
  have hstepnorm :
      ‖(x - xstar) - η • g‖ ^ 2 =
        ‖x - xstar‖ ^ 2 - 2 * η * ⟪g, x - xstar⟫_ℝ +
          η ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_sub_sq_real, hinner_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hη]
    ring
  rw [hrewrite, hstepnorm] at hproj_sq
  exact hproj_sq

/-- One expected projected-SGD step with bias controlled at the mean gradient. -/
theorem projected_biased_gradient_step_expectation
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x xstar grad : E) (xnext g : Ω → E) (η gap B M : ℝ)
    (hη : 0 ≤ η)
    (hg : Integrable g μ)
    (hgsq : Integrable (fun ω ↦ ‖g ω‖ ^ 2) μ)
    (hnext : Integrable (fun ω ↦ ‖xnext ω - xstar‖ ^ 2) μ)
    (hprojection : ∀ ω, ‖xnext ω - xstar‖ ≤ ‖(x - η • g ω) - xstar‖)
    (hstrong : gap + (1 / 2 : ℝ) * ‖x - xstar‖ ^ 2 ≤
      ⟪grad, x - xstar⟫_ℝ)
    (hbias : ‖(∫ ω, g ω ∂μ) - grad‖ ≤ B)
    (hmoment : ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ M) :
    ∫ ω, ‖xnext ω - xstar‖ ^ 2 ∂μ ≤
      (1 - η / 2) * ‖x - xstar‖ ^ 2 - 2 * η * gap +
        2 * η * B ^ 2 + η ^ 2 * M := by
  let displacement : E := x - xstar
  have hinnerInt : Integrable (fun ω ↦ ⟪g ω, displacement⟫_ℝ) μ :=
    hg.inner_const displacement
  have hrhs : Integrable
      (fun ω ↦ ‖displacement‖ ^ 2 - 2 * η * ⟪g ω, displacement⟫_ℝ +
        η ^ 2 * ‖g ω‖ ^ 2) μ := by
    fun_prop
  have hraw : ∫ ω, ‖xnext ω - xstar‖ ^ 2 ∂μ ≤
      ∫ ω, (‖displacement‖ ^ 2 - 2 * η * ⟪g ω, displacement⟫_ℝ +
        η ^ 2 * ‖g ω‖ ^ 2) ∂μ := by
    refine integral_mono_ae hnext hrhs ?_
    filter_upwards with ω
    simpa only [displacement] using
      projected_gradient_step_raw x xstar (xnext ω) (g ω) η hη (hprojection ω)
  have hinnerIntegral :
      ∫ ω, ⟪g ω, displacement⟫_ℝ ∂μ = ⟪(∫ ω, g ω ∂μ), displacement⟫_ℝ := by
    calc
      ∫ ω, ⟪g ω, displacement⟫_ℝ ∂μ =
          ∫ ω, ⟪displacement, g ω⟫_ℝ ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            rw [real_inner_comm]
      _ = ⟪displacement, ∫ ω, g ω ∂μ⟫_ℝ := integral_inner hg displacement
      _ = ⟪(∫ ω, g ω ∂μ), displacement⟫_ℝ := real_inner_comm _ _
  have hrhsIntegral :
      ∫ ω, (‖displacement‖ ^ 2 - 2 * η * ⟪g ω, displacement⟫_ℝ +
          η ^ 2 * ‖g ω‖ ^ 2) ∂μ =
        ‖displacement‖ ^ 2 - 2 * η *
            ⟪(∫ ω, g ω ∂μ), displacement⟫_ℝ +
          η ^ 2 * (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
    have hsubInt : Integrable
        (fun ω ↦ ‖displacement‖ ^ 2 - 2 * η * ⟪g ω, displacement⟫_ℝ) μ :=
      (integrable_const _).sub (hinnerInt.const_mul (2 * η))
    have hnoiseInt : Integrable (fun ω ↦ η ^ 2 * ‖g ω‖ ^ 2) μ :=
      hgsq.const_mul (η ^ 2)
    rw [integral_add hsubInt hnoiseInt]
    rw [integral_sub (integrable_const _) (hinnerInt.const_mul (2 * η))]
    rw [integral_const, integral_const_mul, integral_const_mul, hinnerIntegral]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  have hmeanInner := biased_gradient_inner_lower grad (∫ ω, g ω ∂μ)
    displacement gap B hstrong hbias
  have hmoment' : η ^ 2 * (∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ η ^ 2 * M :=
    mul_le_mul_of_nonneg_left hmoment (sq_nonneg η)
  rw [hrhsIntegral] at hraw
  dsimp only [displacement] at hraw hmeanInner
  nlinarith

/-- Rearrangement of the expected one-step inequality at the manuscript's
stepsize `η_k = 4 / (k + 2)`. -/
theorem expected_projected_step_rearranged
    (k : ℕ) (R Rnext Δ B M : ℝ)
    (hstep : Rnext ≤
      (1 - (4 / (k + 2 : ℝ)) / 2) * R -
        2 * (4 / (k + 2 : ℝ)) * Δ +
        2 * (4 / (k + 2 : ℝ)) * B ^ 2 +
        (4 / (k + 2 : ℝ)) ^ 2 * M) :
    Δ ≤ ((k : ℝ) * R - (k + 2 : ℝ) * Rnext) / 8 +
      B ^ 2 + 2 * M / (k + 2) := by
  have hk2 : (0 : ℝ) < k + 2 := by positivity
  field_simp [ne_of_gt hk2] at hstep ⊢
  nlinarith

/-- The expected projected-step recurrences imply the exact weighted sum
used by the SGD telescope. -/
theorem biased_sgd_weighted_sum_of_expected_steps
    (n : ℕ) (R Δ : ℕ → ℝ) (B M : ℝ)
    (hM : 0 ≤ M) (hR : ∀ t, 0 ≤ R t)
    (hstep : ∀ k < n,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) * Δ (k + 1) +
          2 * (4 / (k + 2 : ℝ)) * B ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 * M) :
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) * Δ (k + 1) ≤
      (n : ℝ) * (n + 1) / 2 * B ^ 2 + 2 * M * n := by
  apply biased_sgd_weighted_sum n R Δ B M hM hR
  intro k hk
  exact expected_projected_step_rearranged k
    (R (k + 1)) (R (k + 2)) (Δ (k + 1)) B M (hstep k hk)

/-- Expected one-step recurrences plus the convex weighted-average comparison
give the final `B² + 4M/(n+1)` guarantee. -/
theorem biased_sgd_final_bound_of_expected_steps
    (n : ℕ) (hn : 0 < n) (R Δ : ℕ → ℝ) (B M gap : ℝ)
    (hM : 0 ≤ M) (hR : ∀ t, 0 ≤ R t)
    (hstep : ∀ k < n,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) * Δ (k + 1) +
          2 * (4 / (k + 2 : ℝ)) * B ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 * M)
    (havg : gap ≤ 2 / ((n : ℝ) * (n + 1)) *
      (∑ k ∈ Finset.range n, (k + 1 : ℝ) * Δ (k + 1))) :
    gap ≤ B ^ 2 + 4 * M / (n + 1) := by
  apply biased_sgd_final_bound n hn
    (∑ k ∈ Finset.range n, (k + 1 : ℝ) * Δ (k + 1)) gap B M
  · exact biased_sgd_weighted_sum_of_expected_steps n R Δ B M hM hR hstep
  · exact havg

end NoisyZO
