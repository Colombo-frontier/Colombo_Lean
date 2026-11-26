import NCBall.NoiseMoments
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Conditional mean zero implies the noise orthogonality needed by the upper bound -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem integral_inner_of_condExp_zero {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgm : AEStronglyMeasurable[m] g μ) (hzero : μ[f | m] =ᵐ[μ] 0) :
    (∫ ω, ⟪f ω, g ω⟫_ℝ ∂μ) = 0 := by
  letI : MeasurableSpace Ω := m₀
  have hgm' : AEStronglyMeasurable[m] (hg.toLp g) μ := hgm.congr hg.coeFn_toLp.symm
  have hc : (condExpL2 E ℝ hm (hf.toLp f) : Lp E 2 μ) = 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mpr ((hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm).trans hzero)
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm (hf.toLp f) (hg.toLp g) hgm'
  rw [hc, inner_zero_left] at hi
  calc
    _ = ⟪hf.toLp f, hg.toLp g⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfw hgw
      rw [hfw, hgw]
    _ = 0 := hi.symm

theorem conditional_noise_mean_zero {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {g a : Ω → E} (hg : MemLp g 2 μ) (ha : MemLp a 2 μ)
    (ham : AEStronglyMeasurable[m] a μ) (hmean : μ[g | m] =ᵐ[μ] a) :
    μ[g - a | m] =ᵐ[μ] 0 := by
  have haa := condExp_of_aestronglyMeasurable' hm ham (ha.integrable (by norm_num))
  filter_upwards [condExp_sub (hg.integrable (by norm_num)) (ha.integrable (by norm_num)) m,
    hmean, haa] with ω hsub hgw haw
  simp only [hsub, Pi.sub_apply, hgw, haw, sub_self, Pi.zero_apply]

theorem conditional_noise_second_moment {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {g a : Ω → E} (hg : MemLp g 2 μ) (ha : MemLp a 2 μ)
    (ham : AEStronglyMeasurable[m] a μ) (hmean : μ[g | m] =ᵐ[μ] a) :
    (∫ ω, ‖g ω - a ω‖ ^ 2 ∂μ) ≤ ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
  letI : MeasurableSpace Ω := m₀
  have hz := conditional_noise_mean_zero (m₀ := m₀) (μ := μ) hm hg ha ham hmean
  have ho := integral_inner_of_condExp_zero (m₀ := m₀) (μ := μ) hm (hg.sub ha) ha ham hz
  have he : (∫ ω, ‖(g - a) ω + a ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖(g - a) ω‖ ^ 2 ∂μ) + ∫ ω, ‖a ω‖ ^ 2 ∂μ :=
    integral_sq_norm_add_of_orthogonal (hg.sub ha) ha ho
  simp only [Pi.sub_apply, sub_add_cancel] at he
  have hn : 0 ≤ ∫ ω, ‖a ω‖ ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  linarith

theorem conditional_noise_pairwise_orthogonal (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ t, m t ≤ m₀) (e : ℕ → Ω → E) (he : ∀ t, MemLp (e t) 2 μ)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[m j] (e i) μ)
    (hzero : ∀ t, μ[e t | m t] =ᵐ[μ] 0) :
    ∀ i j, i < j → (∫ ω, ⟪e i ω, e j ω⟫_ℝ ∂μ) = 0 := by
  intro i j hij
  calc
    _ = ∫ ω, ⟪e j ω, e i ω⟫_ℝ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => real_inner_comm (e j ω) (e i ω))
    _ = 0 := integral_inner_of_condExp_zero (hm j) (he j) (he i) (hpast i j hij) (hzero j)

theorem integral_norm_conditional_noise_sum_le [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ m₀)
    (e : ℕ → Ω → E) (he : ∀ t, MemLp (e t) 2 μ)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[m j] (e i) μ)
    (hzero : ∀ t, μ[e t | m t] =ᵐ[μ] 0)
    {V : ℝ} (hV : ∀ t, (∫ ω, ‖e t ω‖ ^ 2 ∂μ) ≤ V ^ 2) (N : ℕ) :
    (∫ ω, ‖∑ t ∈ Finset.range N, e t ω‖ ∂μ) ≤ Real.sqrt (N : ℝ) * |V| :=
  integral_norm_noise_sum_le e he (conditional_noise_pairwise_orthogonal m hm e he hpast hzero) hV N

end NCBall
