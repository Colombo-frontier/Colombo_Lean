import NCBall.UpperBlock
import NCBall.ConditionalNoise

/-! # Expectation bounds for the actual clipped iteration

The pointwise online estimate is integrated with all integrability conditions
proved. The final theorem derives the noise term from conditional unbiasedness
and past measurability, rather than assuming independent noise vectors.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω}

theorem clippedIncrement_aestronglyMeasurable (D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (g : ℕ → Ω → E) (hg : ∀ t, AEStronglyMeasurable (g t) μ) (t : ℕ) :
    AEStronglyMeasurable (fun ω => clippedIncrement D hD α (fun s => g s ω) t) μ := by
  induction t with
  | zero => exact aestronglyMeasurable_const
  | succ t ih =>
    exact (ballProjection_lipschitz D hD).continuous.comp_aestronglyMeasurable
      (ih.sub ((hg t).const_smul α))

theorem clippedIncrement_memLp [IsFiniteMeasure μ] (D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (g : ℕ → Ω → E) (hg : ∀ t, AEStronglyMeasurable (g t) μ) (t : ℕ) :
    MemLp (fun ω => clippedIncrement D hD α (fun s => g s ω) t) 2 μ :=
  MemLp.of_bound (clippedIncrement_aestronglyMeasurable D hD α g hg t) D
    (Filter.Eventually.of_forall (fun ω => clippedIncrement_norm_le D hD α (fun s => g s ω) t))

theorem expected_clipped_block_bound [IsProbabilityMeasure μ]
    {D α V : ℝ} (hD : 0 ≤ D) (hα : 0 < α) (g a : ℕ → Ω → E)
    (hg : ∀ t, MemLp (g t) 2 μ) (ha : ∀ t, MemLp (a t) 2 μ)
    (hV : ∀ t, (∫ ω, ‖g t ω‖ ^ 2 ∂μ) ≤ V ^ 2) (s T : ℕ)
    (hnoise : (∫ ω, ‖∑ t ∈ Finset.range T, (g (s + t) ω - a (s + t) ω)‖ ∂μ) ≤
      Real.sqrt (T : ℝ) * |V|) :
    D * (∫ ω, ‖∑ t ∈ Finset.range T, a (s + t) ω‖ ∂μ) ≤
      2 * D ^ 2 / α + (α / 2) * (T : ℝ) * V ^ 2 -
        (∫ ω, ∑ t ∈ Finset.range T,
          ⟪g (s + t) ω, clippedIncrement D hD α (fun j => g j ω) (s + t)⟫_ℝ ∂μ) +
        D * (Real.sqrt (T : ℝ) * |V|) := by
  let Q := fun ω => ∑ t ∈ Finset.range T, ‖g (s + t) ω‖ ^ 2
  let L := fun ω => ∑ t ∈ Finset.range T,
    ⟪g (s + t) ω, clippedIncrement D hD α (fun j => g j ω) (s + t)⟫_ℝ
  let Z := fun ω => ‖∑ t ∈ Finset.range T, (g (s + t) ω - a (s + t) ω)‖
  let A := fun ω => ‖∑ t ∈ Finset.range T, a (s + t) ω‖
  have hQ : Integrable Q μ :=
    integrable_finset_sum _ (fun t _ => (hg (s + t)).norm.integrable_sq)
  have hL : Integrable L μ := integrable_finset_sum _ (fun t _ =>
    integrable_inner_of_memLp (hg (s + t))
      (clippedIncrement_memLp D hD α g (fun j => (hg j).1) (s + t)))
  have hZ : Integrable Z μ :=
    (memLp_finset_sum (Finset.range T) (fun t _ => (hg (s + t)).sub (ha (s + t)))).norm.integrable
      (by norm_num)
  have hA : Integrable A μ :=
    (memLp_finset_sum (Finset.range T) (fun t _ => ha (s + t))).norm.integrable (by norm_num)
  have hC : Integrable (fun ω => 2 * D ^ 2 / α + (α / 2) * Q ω) μ :=
    (integrable_const _).add (hQ.const_mul _)
  have hR : Integrable (fun ω => 2 * D ^ 2 / α + (α / 2) * Q ω - L ω) μ := hC.sub hL
  have hb := integral_mono (hA.const_mul D) (hR.add (hZ.const_mul D))
    (fun ω => clipped_block_gradient_norm hD hα (fun j => g j ω) (fun j => a j ω) s T)
  change (∫ ω, D * A ω ∂μ) ≤
    ∫ ω, (2 * D ^ 2 / α + (α / 2) * Q ω - L ω) + D * Z ω ∂μ at hb
  rw [integral_const_mul, integral_add hR (hZ.const_mul D), integral_sub hC hL,
    integral_add (integrable_const _) (hQ.const_mul _), integral_const_mul, integral_const_mul,
    integral_const] at hb
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at hb
  have hQB : (∫ ω, Q ω ∂μ) ≤ (T : ℝ) * V ^ 2 := by
    rw [integral_finset_sum _ (fun t _ => (hg (s + t)).norm.integrable_sq)]
    calc
      _ ≤ ∑ _t ∈ Finset.range T, V ^ 2 := Finset.sum_le_sum (fun t _ => hV (s + t))
      _ = _ := by simp
  have hmQ := mul_le_mul_of_nonneg_left hQB (show 0 ≤ α / 2 by positivity)
  have hmZ := mul_le_mul_of_nonneg_left hnoise hD
  change D * (∫ ω, A ω ∂μ) ≤ _
  change D * (∫ ω, Z ω ∂μ) ≤ _ at hmZ
  change D * (∫ ω, A ω ∂μ) ≤
    2 * D ^ 2 / α + (α / 2) * (T : ℝ) * V ^ 2 - (∫ ω, L ω ∂μ) +
      D * (Real.sqrt (T : ℝ) * |V|)
  linarith

theorem expected_clipped_block_of_conditional_unbiased [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ m₀)
    {D α V : ℝ} (hD : 0 ≤ D) (hα : 0 < α) (g a : ℕ → Ω → E)
    (hg : ∀ t, MemLp (g t) 2 μ) (ha : ∀ t, MemLp (a t) 2 μ)
    (ham : ∀ t, AEStronglyMeasurable[m t] (a t) μ)
    (hmean : ∀ t, μ[g t | m t] =ᵐ[μ] a t)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[m j] (g i - a i) μ)
    (hV : ∀ t, (∫ ω, ‖g t ω‖ ^ 2 ∂μ) ≤ V ^ 2) (s T : ℕ) :
    D * (∫ ω, ‖∑ t ∈ Finset.range T, a (s + t) ω‖ ∂μ) ≤
      2 * D ^ 2 / α + (α / 2) * (T : ℝ) * V ^ 2 -
        (∫ ω, ∑ t ∈ Finset.range T,
          ⟪g (s + t) ω, clippedIncrement D hD α (fun j => g j ω) (s + t)⟫_ℝ ∂μ) +
        D * (Real.sqrt (T : ℝ) * |V|) := by
  apply expected_clipped_block_bound hD hα g a hg ha hV s T
  apply integral_norm_conditional_noise_sum_le (fun t => m (s + t)) (fun t => hm (s + t))
    (fun t => g (s + t) - a (s + t)) (fun t => (hg (s + t)).sub (ha (s + t)))
  · intro i j hij
    exact hpast (s + i) (s + j) (by omega)
  · intro t
    exact conditional_noise_mean_zero (m₀ := m₀) (μ := μ) (hm (s + t))
      (hg (s + t)) (ha (s + t)) (ham (s + t)) (hmean (s + t))
  · intro t
    exact (conditional_noise_second_moment (m₀ := m₀) (μ := μ) (hm (s + t))
      (hg (s + t)) (ha (s + t)) (ham (s + t)) (hmean (s + t))).trans (hV (s + t))

end NCBall
