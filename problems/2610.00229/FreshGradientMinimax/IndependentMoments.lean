import FreshGradientMinimax.Probability
import Mathlib.MeasureTheory.Integral.Prod

/-! Moment identities on actual independent product distributions. These
lemmas provide the analytic basis for fresh minibatches and finite levels. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped InnerProductSpace

variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure A} {ξ : Measure B} [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem integrable_on_product_fst {f : A → E} (hf : Integrable f ν) :
    Integrable (fun z : A × B => f z.1) (ν.prod ξ) := by
  have hm : Measure.map Prod.fst (ν.prod ξ) = ν := by simp
  have hh : Integrable f (Measure.map Prod.fst (ν.prod ξ)) := hm.symm ▸ hf
  exact hh.comp_measurable measurable_fst

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem integrable_on_product_snd {g : B → E} (hg : Integrable g ξ) :
    Integrable (fun z : A × B => g z.2) (ν.prod ξ) := by
  have hm : Measure.map Prod.snd (ν.prod ξ) = ξ := by simp
  have hh : Integrable g (Measure.map Prod.snd (ν.prod ξ)) := hm.symm ▸ hg
  exact hh.comp_measurable measurable_snd

omit [CompleteSpace E] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] in
theorem independent_inner_integrable {f : A → E} {g : B → E}
    (hf : Integrable f ν) (hg : Integrable g ξ) :
    Integrable (fun z : A × B => ⟪f z.1, g z.2⟫_ℝ) (ν.prod ξ) := by
  exact hf.op_fst_snd (continuous_inner (𝕜 := ℝ))
    ⟨1, by intro x y; simpa using (norm_inner_le_norm (𝕜 := ℝ) x y)⟩ hg

theorem independent_inner_mean {f : A → E} {g : B → E}
    (hf : Integrable f ν) (hg : Integrable g ξ) :
    (∫ z : A × B, ⟪f z.1, g z.2⟫_ℝ ∂ν.prod ξ) = ⟪∫ a, f a ∂ν, ∫ b, g b ∂ξ⟫_ℝ := by
  rw [integral_prod _ (independent_inner_integrable hf hg)]
  simp_rw [integral_inner hg]
  calc
    _ = ∫ a, ⟪∫ b, g b ∂ξ, f a⟫_ℝ ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => real_inner_comm _ _)
    _ = _ := by rw [integral_inner hf, real_inner_comm]

omit [CompleteSpace E] in
theorem independent_sum_square_integrable {f : A → E} {g : B → E}
    (hf : Integrable f ν) (hg : Integrable g ξ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ν) (hg2 : Integrable (fun b => ‖g b‖ ^ 2) ξ) :
    Integrable (fun z : A × B => ‖f z.1 + g z.2‖ ^ 2) (ν.prod ξ) := by
  have hi := independent_inner_integrable hf hg
  have h1 := integrable_on_product_fst (ξ := ξ) hf2
  have h2 := integrable_on_product_snd (ν := ν) hg2
  simpa only [norm_add_sq_real] using (h1.add (hi.const_mul 2)).add h2

omit [CompleteSpace E] in
theorem independent_sum_mean {f : A → E} {g : B → E}
    (hf : Integrable f ν) (hg : Integrable g ξ) :
    (∫ z : A × B, f z.1 + g z.2 ∂ν.prod ξ) = (∫ a, f a ∂ν) + ∫ b, g b ∂ξ := by
  rw [integral_add (integrable_on_product_fst hf) (integrable_on_product_snd hg)]
  simp [integral_fun_fst, integral_fun_snd]

theorem independent_sum_second_moment {f : A → E} {g : B → E}
    (hf : Integrable f ν) (hg : Integrable g ξ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ν) (hg2 : Integrable (fun b => ‖g b‖ ^ 2) ξ) :
    (∫ z : A × B, ‖f z.1 + g z.2‖ ^ 2 ∂ν.prod ξ) =
      (∫ a, ‖f a‖ ^ 2 ∂ν) + 2 * ⟪∫ a, f a ∂ν, ∫ b, g b ∂ξ⟫_ℝ + ∫ b, ‖g b‖ ^ 2 ∂ξ := by
  have hi := independent_inner_integrable hf hg
  have h1 : Integrable (fun z : A × B => ‖f z.1‖ ^ 2) (ν.prod ξ) := integrable_on_product_fst hf2
  have h2 : Integrable (fun z : A × B => ‖g z.2‖ ^ 2) (ν.prod ξ) := integrable_on_product_snd hg2
  have h12 : Integrable (fun z : A × B => ‖f z.1‖ ^ 2 + 2 * ⟪f z.1, g z.2⟫_ℝ) (ν.prod ξ) :=
    h1.add (hi.const_mul 2)
  simp_rw [norm_add_sq_real]
  rw [integral_add h12 h2, integral_add h1 (hi.const_mul 2), integral_const_mul,
    independent_inner_mean hf hg]
  rw [integral_fun_fst (fun a => ‖f a‖ ^ 2), integral_fun_snd (fun b => ‖g b‖ ^ 2)]
  simp

omit [IsProbabilityMeasure ξ] [CompleteSpace E] in
theorem integrable_square_add_const {f : A → E} (hf : Integrable f ν)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ν) (c : E) :
    Integrable (fun a => ‖f a + c‖ ^ 2) ν := by
  simpa only [norm_add_sq_real] using
    (hf2.add ((hf.inner_const c).const_mul 2)).add (integrable_const (‖c‖ ^ 2))

omit [IsProbabilityMeasure ξ] [CompleteSpace E] in
theorem integrable_square_sub_const {f : A → E} (hf : Integrable f ν)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ν) (c : E) :
    Integrable (fun a => ‖f a - c‖ ^ 2) ν := by
  simpa only [sub_eq_add_neg] using integrable_square_add_const hf hf2 (-c)

omit [IsProbabilityMeasure ξ] [CompleteSpace E] in
theorem square_integrable_of_centered {f : A → E} (hf : Integrable f ν) (c : E)
    (hc : Integrable (fun a => ‖f a - c‖ ^ 2) ν) : Integrable (fun a => ‖f a‖ ^ 2) ν := by
  have h := integrable_square_add_const (hf.sub (integrable_const c)) hc c
  simpa only [sub_add_cancel, Pi.sub_apply] using h

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure ξ] in
theorem integrable_of_centered_square {f : A → E} (hf : AEStronglyMeasurable f ν) (c : E)
    (hc : Integrable (fun a => ‖f a - c‖ ^ 2) ν) : Integrable f ν := by
  have hbound : Integrable (fun a => ‖f a - c‖ ^ 2 + (1 + ‖c‖)) ν := hc.add (integrable_const _)
  apply hbound.mono' hf
  apply Filter.Eventually.of_forall
  intro a
  have ht := norm_add_le (f a - c) c
  rw [sub_add_cancel] at ht
  nlinarith [sq_nonneg (‖f a - c‖ - 1 / 2)]

end FreshGradientMinimax
