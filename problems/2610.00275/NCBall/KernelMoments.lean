import NCBall.NoiseMoments
import Mathlib.MeasureTheory.Integral.Prod

/-! # Uniform second moments of a measurable oracle kernel -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace NCBall

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Ω} {μ : Measure Ξ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem kernel_memLp_two (G : Ω → Ξ → E)
    (hG : Measurable (fun w : Ω × Ξ => G w.1 w.2))
    (hG2 : ∀ w, MemLp (G w) 2 μ) {V : ℝ}
    (hV : ∀ w, (∫ z, ‖G w z‖ ^ 2 ∂μ) ≤ V ^ 2) :
    MemLp (fun w : Ω × Ξ => G w.1 w.2) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).2
  have hm : AEStronglyMeasurable (fun w : Ω × Ξ => ‖G w.1 w.2‖ ^ 2) (ν.prod μ) :=
    (hG.norm.pow_const 2).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  refine ⟨Filter.Eventually.of_forall (fun w => (hG2 w).norm.integrable_sq), ?_⟩
  apply (integrable_const (V ^ 2)).mono' hm.norm.integral_prod_right'
  filter_upwards [] with w
  simp only [Real.norm_eq_abs, abs_sq]
  rw [abs_of_nonneg (integral_nonneg (fun z => sq_nonneg ‖G w z‖))]
  exact hV w

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem kernel_second_moment (G : Ω → Ξ → E)
    (hG : Measurable (fun w : Ω × Ξ => G w.1 w.2))
    (hG2 : ∀ w, MemLp (G w) 2 μ) {V : ℝ}
    (hV : ∀ w, (∫ z, ‖G w z‖ ^ 2 ∂μ) ≤ V ^ 2) :
    (∫ w : Ω × Ξ, ‖G w.1 w.2‖ ^ 2 ∂ν.prod μ) ≤ V ^ 2 := by
  have hi := (kernel_memLp_two (ν := ν) G hG hG2 hV).norm.integrable_sq
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _w, V ^ 2 ∂ν := integral_mono hi.integral_prod_left (integrable_const _)
      (fun w => hV w)
    _ = _ := by simp

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem centered_kernel_mean_zero (g : Ξ → E) (hg : MemLp g 2 μ) (a : E)
    (ha : (∫ z, g z ∂μ) = a) : (∫ z, g z - a ∂μ) = 0 := by
  rw [integral_sub (hg.integrable (by norm_num)) (integrable_const _), ha]
  simp

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem centered_kernel_second_moment (g : Ξ → E) (hg : MemLp g 2 μ) (a : E)
    (ha : (∫ z, g z ∂μ) = a) :
    (∫ z, ‖g z - a‖ ^ 2 ∂μ) ≤ ∫ z, ‖g z‖ ^ 2 ∂μ := by
  have he : MemLp (fun z => g z - a) 2 μ := hg.sub (memLp_const a)
  have hz : (∫ z, ⟪g z - a, a⟫_ℝ ∂μ) = 0 := by
    simp_rw [real_inner_comm a]
    rw [integral_inner (he.integrable (by norm_num)), centered_kernel_mean_zero g hg a ha]
    simp
  have hid := integral_sq_norm_add_of_orthogonal he (memLp_const a) hz
  simp only [sub_add_cancel, integral_const, measureReal_univ_eq_one, one_smul] at hid
  nlinarith [sq_nonneg ‖a‖]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem kernel_mean_norm_le (g : Ξ → E) (hg : MemLp g 2 μ) (a : E)
    (ha : (∫ z, g z ∂μ) = a) {V : ℝ}
    (hV : (∫ z, ‖g z‖ ^ 2 ∂μ) ≤ V ^ 2) : ‖a‖ ≤ |V| := by
  have hnorm : ‖a‖ ≤ ∫ z, ‖g z‖ ∂μ := ha ▸ norm_integral_le_integral_norm g
  have hs := integral_norm_sq_le_second_moment hg
  have hp : 0 ≤ ∫ z, ‖g z‖ ∂μ := integral_nonneg (fun z => norm_nonneg (g z))
  nlinarith [sq_abs V, abs_nonneg V, norm_nonneg a]

end NCBall
