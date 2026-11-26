import NCBall.UpperDescent

/-! # Block convergence bounds for the actual iid first-order algorithm -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators unitInterval
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {G : E → Ξ → E} {f : E → ℝ} {V : ℝ}

theorem upper_step_difference_integrable (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    Integrable (fun w : UpperRandomness Ξ =>
      f (upperState D hD α G x₀ w.1 w.2 (t + 1)).1 - f (upperState D hD α G x₀ w.1 w.2 t).1)
      (upperPoolLaw μ) := by
  let x := fun w : UpperRandomness Ξ => (upperState D hD α G x₀ w.1 w.2 t).1
  let v := fun w : UpperRandomness Ξ => (upperState D hD α G x₀ w.1 w.2 t).2
  have hm := upperState_measurable D hD α G ho.measurable x₀ t
  have hb : ∀ w, ‖v w‖ ≤ D := by
    intro w
    dsimp only [v]
    rw [upper_increment_eq_clipped]
    exact clippedIncrement_norm_le D hD α _ t
  have hg : ∀ y, ‖gradient f y‖ ≤ |V| := fun y =>
    kernel_mean_norm_le _ (ho.square_integrable y) _ (ho.mean y) (ho.moment y)
  have hi := random_segment_integrable (upperPoolLaw μ) hf (abs_nonneg V) hD hg x v hm.fst hm.snd hb
  apply hi.integral_prod_left.congr
  exact Filter.Eventually.of_forall (fun w => unit_segment_gradient_integral hf (x w) (v w))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
theorem upper_block_telescope (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E)
    (w : UpperRandomness Ξ) (s T : ℕ) :
    (∑ t ∈ Finset.range T,
      (f (upperState D hD α G x₀ w.1 w.2 (s + t + 1)).1 - f (upperState D hD α G x₀ w.1 w.2 (s + t)).1)) =
      f (upperState D hD α G x₀ w.1 w.2 (s + T)).1 - f (upperState D hD α G x₀ w.1 w.2 s).1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show s + (T + 1) = s + T + 1 by omega]
    ring

theorem upper_block_difference_integrable (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (s T : ℕ) :
    Integrable (fun w : UpperRandomness Ξ =>
      f (upperState D hD α G x₀ w.1 w.2 (s + T)).1 - f (upperState D hD α G x₀ w.1 w.2 s).1)
      (upperPoolLaw μ) := by
  have hi := integrable_finset_sum (Finset.range T)
    (fun t _ => upper_step_difference_integrable hf ho D hD α x₀ (s + t))
  simpa only [upper_block_telescope] using hi

theorem upper_block_expected_descent (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (s T : ℕ) :
    (∫ w : UpperRandomness Ξ, ∑ t ∈ Finset.range T,
      ⟪upperEstimate D hD α G x₀ w.1 w.2 (s + t),
        clippedIncrement D hD α (upperEstimate D hD α G x₀ w.1 w.2) (s + t)⟫_ℝ ∂upperPoolLaw μ) =
      ∫ w : UpperRandomness Ξ,
        (f (upperState D hD α G x₀ w.1 w.2 (s + T)).1 - f (upperState D hD α G x₀ w.1 w.2 s).1)
          ∂upperPoolLaw μ := by
  simp_rw [← upper_increment_eq_clipped]
  rw [integral_finset_sum _ (fun t _ => integrable_inner_of_memLp
    (upperEstimate_memLp ho D hD α x₀ (s + t)) (upperIncrement_memLp ho D hD α x₀ (s + t)))]
  simp_rw [upper_expected_descent hf ho]
  rw [← integral_finset_sum _ (fun t _ => upper_step_difference_integrable hf ho D hD α x₀ (s + t))]
  simp only [upper_block_telescope]

theorem upper_expected_block_gradient (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    {D α : ℝ} (hD : 0 ≤ D) (hα : 0 < α) (x₀ : E) (s T : ℕ) :
    D * (∫ w : UpperRandomness Ξ, ‖∑ t ∈ Finset.range T,
      gradient f (upperLocation D hD α G x₀ w.1 w.2 (s + t))‖ ∂upperPoolLaw μ) ≤
      2 * D ^ 2 / α + (α / 2) * (T : ℝ) * V ^ 2 -
        (∫ w : UpperRandomness Ξ,
          (f (upperState D hD α G x₀ w.1 w.2 (s + T)).1 - f (upperState D hD α G x₀ w.1 w.2 s).1)
            ∂upperPoolLaw μ) + D * (Real.sqrt (T : ℝ) * |V|) := by
  have hb := expected_clipped_block_bound hD hα
    (fun t (w : UpperRandomness Ξ) => upperEstimate D hD α G x₀ w.1 w.2 t)
    (fun t (w : UpperRandomness Ξ) => gradient f (upperLocation D hD α G x₀ w.1 w.2 t))
    (fun t => upperEstimate_memLp ho D hD α x₀ t)
    (fun t => upperMean_memLp ho D hD α x₀ t)
    (fun t => upperEstimate_second_moment ho D hD α x₀ t) s T
    (upperNoise_block_norm ho D hD α x₀ s T)
  rwa [upper_block_expected_descent hf ho] at hb

end NCBall
