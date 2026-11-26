import NCBall.UpperSampling
import NCBall.UpperExpectation

/-! # Expected descent of the actual independently sampled process -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace unitInterval BigOperators
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {G : E → Ξ → E} {a : E → E} {V : ℝ}

theorem upperIncrement_memLp (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    MemLp (fun w : UpperRandomness Ξ => (upperState D hD α G x₀ w.1 w.2 t).2) 2 (upperPoolLaw μ) := by
  apply MemLp.of_bound (upperState_measurable D hD α G ho.measurable x₀ t).snd.aestronglyMeasurable D
  filter_upwards [] with w
  rw [upper_increment_eq_clipped]
  exact clippedIncrement_norm_le D hD α _ t

theorem upperEstimate_inner_mean (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    (∫ w : UpperRandomness Ξ,
      ⟪upperEstimate D hD α G x₀ w.1 w.2 t, (upperState D hD α G x₀ w.1 w.2 t).2⟫_ℝ
        ∂upperPoolLaw μ) =
      ∫ w : UpperRandomness Ξ,
        ⟪a (upperLocation D hD α G x₀ w.1 w.2 t), (upperState D hD α G x₀ w.1 w.2 t).2⟫_ℝ
          ∂upperPoolLaw μ := by
  apply resampled_inner_unbiased (upper_noise_refresh_preserves μ t) _ _ _
    (upperEstimate_memLp ho D hD α x₀ t) (upperMean_memLp ho D hD α x₀ t)
    (upperIncrement_memLp ho D hD α x₀ t)
    (fun w ξ => G (upperLocation D hD α G x₀ w.1 w.2 t) ξ)
    (fun w => ho.square_integrable _) (fun w => ho.mean _)
  · exact fun w ξ => upperEstimate_noise_refresh D hD α G x₀ w.1 w.2 t ξ
  · intro w ξ
    dsimp only
    rw [upperLocation_noise_refresh D hD α G x₀ w.1 w.2 t ξ le_rfl]
  · intro w ξ
    dsimp only
    rw [upperState_noise_refresh D hD α G x₀ w.1 w.2 t ξ t le_rfl]

theorem upper_gradient_descent {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    (∫ w : UpperRandomness Ξ,
      ⟪gradient f (upperLocation D hD α G x₀ w.1 w.2 t), (upperState D hD α G x₀ w.1 w.2 t).2⟫_ℝ
        ∂upperPoolLaw μ) =
      ∫ w : UpperRandomness Ξ,
        (f (upperState D hD α G x₀ w.1 w.2 (t + 1)).1 - f (upperState D hD α G x₀ w.1 w.2 t).1)
          ∂upperPoolLaw μ := by
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
  have horig := integrable_inner_of_memLp (upperMean_memLp ho D hD α x₀ t)
    (upperIncrement_memLp ho D hD α x₀ t)
  rw [integral_refresh (upper_segment_refresh_preserves μ t) horig.aestronglyMeasurable]
  have href (w : UpperRandomness Ξ) (r : I) :
      upperLocation D hD α G x₀ (Function.update w.1 t r) w.2 t = x w + (r : ℝ) • v w := by
    simp only [upperLocation, upperState_segment_refresh D hD α G x₀ w.1 w.2 t r t le_rfl,
      Function.update_self, x, v]
  simp only [href, upperState_segment_refresh D hD α G x₀ _ _ t _ t le_rfl]
  exact random_segment_descent (upperPoolLaw μ) hf x v hi

theorem upper_expected_descent {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    (∫ w : UpperRandomness Ξ,
      ⟪upperEstimate D hD α G x₀ w.1 w.2 t, (upperState D hD α G x₀ w.1 w.2 t).2⟫_ℝ
        ∂upperPoolLaw μ) =
      ∫ w : UpperRandomness Ξ,
        (f (upperState D hD α G x₀ w.1 w.2 (t + 1)).1 - f (upperState D hD α G x₀ w.1 w.2 t).1)
          ∂upperPoolLaw μ :=
  (upperEstimate_inner_mean ho D hD α x₀ t).trans (upper_gradient_descent hf ho D hD α x₀ t)

end NCBall
