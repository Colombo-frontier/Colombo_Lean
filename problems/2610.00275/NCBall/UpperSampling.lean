import NCBall.UpperPool
import NCBall.Resampling

/-! # Actual iid oracle samples have bounded, orthogonal errors

`OracleMoments` is the explicit first-order oracle contract. These results
derive moments for adaptive queries from this pointwise contract and the
independent pools, without assuming martingale properties of the process.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace unitInterval
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]

structure OracleMoments (μ : Measure Ξ) (G : E → Ξ → E) (a : E → E) (V : ℝ) : Prop where
  measurable : Measurable (fun xz : E × Ξ => G xz.1 xz.2)
  mean_measurable : Measurable a
  square_integrable : ∀ x, MemLp (G x) 2 μ
  mean : ∀ x, (∫ z, G x z ∂μ) = a x
  moment : ∀ x, (∫ z, ‖G x z‖ ^ 2 ∂μ) ≤ V ^ 2

variable {G : E → Ξ → E} {a : E → E} {V : ℝ}

theorem upperEstimate_memLp (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    MemLp (fun w : UpperRandomness Ξ => upperEstimate D hD α G x₀ w.1 w.2 t) 2 (upperPoolLaw μ) := by
  let z := fun w : UpperRandomness Ξ => upperLocation D hD α G x₀ w.1 w.2 t
  have hz : Measurable z := upperLocation_measurable D hD α G ho.measurable x₀ t
  exact resampled_oracle_memLp (upper_noise_refresh_preserves μ t) _
    (upperEstimate_measurable D hD α G ho.measurable x₀ t) (fun w ξ => G (z w) ξ)
    (ho.measurable.comp ((hz.comp measurable_fst).prodMk measurable_snd))
    (fun w ξ => upperEstimate_noise_refresh D hD α G x₀ w.1 w.2 t ξ)
    (fun w => ho.square_integrable (z w)) (fun w => ho.moment (z w))

theorem upperEstimate_second_moment (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    (∫ w : UpperRandomness Ξ, ‖upperEstimate D hD α G x₀ w.1 w.2 t‖ ^ 2 ∂upperPoolLaw μ) ≤ V ^ 2 := by
  let z := fun w : UpperRandomness Ξ => upperLocation D hD α G x₀ w.1 w.2 t
  have hz : Measurable z := upperLocation_measurable D hD α G ho.measurable x₀ t
  exact resampled_oracle_second_moment (upper_noise_refresh_preserves μ t) _
    (upperEstimate_measurable D hD α G ho.measurable x₀ t) (fun w ξ => G (z w) ξ)
    (ho.measurable.comp ((hz.comp measurable_fst).prodMk measurable_snd))
    (fun w ξ => upperEstimate_noise_refresh D hD α G x₀ w.1 w.2 t ξ)
    (fun w => ho.square_integrable (z w)) (fun w => ho.moment (z w))

theorem upperMean_memLp (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    MemLp (fun w : UpperRandomness Ξ => a (upperLocation D hD α G x₀ w.1 w.2 t)) 2 (upperPoolLaw μ) := by
  apply MemLp.of_bound (ho.mean_measurable.comp
    (upperLocation_measurable D hD α G ho.measurable x₀ t)).aestronglyMeasurable |V|
  exact Filter.Eventually.of_forall (fun w =>
    kernel_mean_norm_le _ (ho.square_integrable _) _ (ho.mean _) (ho.moment _))

theorem upperNoise_second_moment (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (t : ℕ) :
    (∫ w : UpperRandomness Ξ,
      ‖upperEstimate D hD α G x₀ w.1 w.2 t - a (upperLocation D hD α G x₀ w.1 w.2 t)‖ ^ 2
        ∂upperPoolLaw μ) ≤ V ^ 2 := by
  let z := fun w : UpperRandomness Ξ => upperLocation D hD α G x₀ w.1 w.2 t
  have hz : Measurable z := upperLocation_measurable D hD α G ho.measurable x₀ t
  apply resampled_oracle_second_moment (upper_noise_refresh_preserves μ t) _
    ((upperEstimate_measurable D hD α G ho.measurable x₀ t).sub (ho.mean_measurable.comp hz))
    (fun w ξ => G (z w) ξ - a (z w))
    ((ho.measurable.comp ((hz.comp measurable_fst).prodMk measurable_snd)).sub
      (ho.mean_measurable.comp (hz.comp measurable_fst)))
  · intro w ξ
    dsimp only [Function.comp_apply, z]
    rw [upperEstimate_noise_refresh, upperLocation_noise_refresh D hD α G x₀ w.1 w.2 t ξ le_rfl]
  · exact fun w => (ho.square_integrable (z w)).sub (memLp_const _)
  · exact fun w => (centered_kernel_second_moment _ (ho.square_integrable (z w)) _
      (ho.mean (z w))).trans (ho.moment (z w))

theorem upperNoise_pairwise_orthogonal (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (i j : ℕ) (hij : i < j) :
    (∫ w : UpperRandomness Ξ,
      ⟪upperEstimate D hD α G x₀ w.1 w.2 i - a (upperLocation D hD α G x₀ w.1 w.2 i),
        upperEstimate D hD α G x₀ w.1 w.2 j - a (upperLocation D hD α G x₀ w.1 w.2 j)⟫_ℝ
        ∂upperPoolLaw μ) = 0 := by
  apply resampled_noise_orthogonal (upper_noise_refresh_preserves μ j) _ _
    ((upperEstimate_memLp ho D hD α x₀ j).sub (upperMean_memLp ho D hD α x₀ j))
    ((upperEstimate_memLp ho D hD α x₀ i).sub (upperMean_memLp ho D hD α x₀ i))
    (fun w ξ => G (upperLocation D hD α G x₀ w.1 w.2 j) ξ -
      a (upperLocation D hD α G x₀ w.1 w.2 j))
  · exact fun w => ((ho.square_integrable _).sub (memLp_const _)).integrable (by norm_num)
  · exact fun w => centered_kernel_mean_zero _ (ho.square_integrable _) _ (ho.mean _)
  · intro w ξ
    dsimp only [Pi.sub_apply]
    rw [upperEstimate_noise_refresh, upperLocation_noise_refresh D hD α G x₀ w.1 w.2 j ξ le_rfl]
  · intro w ξ
    dsimp only [Pi.sub_apply]
    rw [upperEstimate_past_noise_refresh D hD α G x₀ w.1 w.2 j ξ hij,
      upperLocation_noise_refresh D hD α G x₀ w.1 w.2 j ξ hij.le]

theorem upperNoise_block_norm (ho : OracleMoments μ G a V)
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E) (s T : ℕ) :
    (∫ w : UpperRandomness Ξ, ‖∑ t ∈ Finset.range T,
      (upperEstimate D hD α G x₀ w.1 w.2 (s + t) - a (upperLocation D hD α G x₀ w.1 w.2 (s + t)))‖
        ∂upperPoolLaw μ) ≤ Real.sqrt (T : ℝ) * |V| := by
  apply integral_norm_noise_sum_le
  · exact fun t => (upperEstimate_memLp ho D hD α x₀ (s + t)).sub
      (upperMean_memLp ho D hD α x₀ (s + t))
  · exact fun i j hij => upperNoise_pairwise_orthogonal ho D hD α x₀ (s + i) (s + j) (by omega)
  · exact fun t => upperNoise_second_moment ho D hD α x₀ (s + t)

end NCBall
