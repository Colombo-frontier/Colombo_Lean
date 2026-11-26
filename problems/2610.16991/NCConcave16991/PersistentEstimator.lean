import NCConcave16991.ConditionalMinibatch
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Abel

/-!
# Persistent estimator increments

The preceding error can depend arbitrarily on the history and is never assumed
centered. Only the fresh sampled difference is centered. The actual product
law makes its cross term with the preceding error vanish.
-/

open Set MeasureTheory InnerProductSpace
open scoped BigOperators InnerProductSpace

namespace NCConcave16991

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
  {n b : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]

theorem minibatch_bias_second_moment (hb : 0 < b) (v : Fin n → H) (bias : H) :
    (∫ I, ‖bias + (minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i)‖ ^ 2 ∂minibatchLaw n b) =
      ‖bias‖ ^ 2 + ∫ I, ‖minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 ∂minibatchLaw n b := by
  let δ := fun I : Fin b → Fin n ↦ minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i
  have hmean : (∫ I, δ I ∂minibatchLaw n b) = 0 := minibatch_centered_integral hb v
  have hcross : (∫ I, ⟪bias, δ I⟫_ℝ ∂minibatchLaw n b) = 0 := by
    have hh := (innerSL ℝ bias).integral_comp_comm
      (Integrable.of_finite : Integrable δ (minibatchLaw n b))
    simpa only [innerSL_apply_apply, hmean, inner_zero_right] using hh
  change (∫ I, ‖bias + δ I‖ ^ 2 ∂minibatchLaw n b) =
    ‖bias‖ ^ 2 + ∫ I, ‖δ I‖ ^ 2 ∂minibatchLaw n b
  simp_rw [norm_add_sq_real]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, hcross]
  simp

theorem AveragedSmooth.persistent_increment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Fin n → E → H} {s : Set E} {L : ℝ} (hG : AveragedSmooth G s L)
    (hb : 0 < b) {x y : E} (hx : x ∈ s) (hy : y ∈ s) (bias : H) :
    (∫ I, ‖bias + (minibatchMean (fun i ↦ G i x - G i y) I -
      (averageMap G x - averageMap G y))‖ ^ 2 ∂minibatchLaw n b) ≤
        ‖bias‖ ^ 2 + (L ^ 2 / b) * ‖x - y‖ ^ 2 := by
  have hdiff : averageMap G x - averageMap G y =
      (n : ℝ)⁻¹ • ∑ i, (G i x - G i y) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  rw [hdiff, minibatch_bias_second_moment hb]
  have hh := hG.minibatch_variance_bound hb hx hy
  rw [hdiff] at hh
  linarith

theorem persistent_update_error_identity
    {E : Type*} {G : Fin n → E → H} (x y : E) (oldEstimate : H) (I : Fin b → Fin n) :
    oldEstimate + minibatchMean (fun i ↦ G i x - G i y) I - averageMap G x =
      (oldEstimate - averageMap G y) +
        (minibatchMean (fun i ↦ G i x - G i y) I - (n : ℝ)⁻¹ • ∑ i, (G i x - G i y)) := by
  simp only [Finset.sum_sub_distrib, smul_sub]
  dsimp [averageMap]
  abel

theorem conditional_persistent_increment_bound
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [SecondCountableTopology H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Fin n → E → H} {s : Set E} {L : ℝ} (hG : AveragedSmooth G s L)
    {x y : Ω → E} (hx : ∀ ω, x ω ∈ s) (hy : ∀ ω, y ω ∈ s)
    (hv : ∀ i, Measurable (fun ω ↦ G i (x ω) - G i (y ω)))
    {bias : Ω → H} (hbias : Measurable bias) (hb : 0 < b)
    (hint : Integrable (fun a ↦ ‖bias a.1 + historyMinibatchError (b := b)
      (fun ω i ↦ G i (x ω) - G i (y ω)) a‖ ^ 2) (μ.prod (minibatchLaw n b))) :
    ∀ᵐ a ∂μ.prod (minibatchLaw n b),
      ((μ.prod (minibatchLaw n b))[(fun a ↦ ‖bias a.1 + historyMinibatchError (b := b)
        (fun ω i ↦ G i (x ω) - G i (y ω)) a‖ ^ 2) |
        mΩ.comap (Prod.fst : Ω × (Fin b → Fin n) → Ω)]) a ≤
        ‖bias a.1‖ ^ 2 + (L ^ 2 / b) * ‖x a.1 - y a.1‖ ^ 2 := by
  have hm : StronglyMeasurable (fun a : Ω × (Fin b → Fin n) ↦
      ‖bias a.1 + historyMinibatchError (b := b)
        (fun ω i ↦ G i (x ω) - G i (y ω)) a‖ ^ 2) := by
    convert (((hbias.comp measurable_fst).add
      (historyMinibatchError_measurable (b := b) hv)).norm.pow_const 2).stronglyMeasurable using 1
    ext a
    rfl
  have he := conditional_product_integral μ (minibatchLaw n b) hm hint
  filter_upwards [he] with a ha
  rw [ha]
  have hdiff : averageMap G (x a.1) - averageMap G (y a.1) =
      (n : ℝ)⁻¹ • ∑ i, (G i (x a.1) - G i (y a.1)) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  simpa only [historyMinibatchError, hdiff] using
    hG.persistent_increment_bound hb (hx a.1) (hy a.1) (bias a.1)

end

end NCConcave16991
