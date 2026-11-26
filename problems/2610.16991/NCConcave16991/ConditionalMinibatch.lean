import NCConcave16991.ConditionalProduct
import NCConcave16991.Minibatch

/-! # Appendix A.1(ii) conditional on history before fresh samples -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991

noncomputable section

variable {Ω H : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {n b : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]

def historyMinibatchError (v : Ω → Fin n → H) (a : Ω × (Fin b → Fin n)) : H :=
  minibatchMean (v a.1) a.2 - (n : ℝ)⁻¹ • ∑ i, v a.1 i

theorem historyMinibatchError_measurable {v : Ω → Fin n → H}
    (hv : ∀ i, Measurable (fun ω ↦ v ω i)) : Measurable (historyMinibatchError (b := b) v) := by
  apply measurable_from_prod_countable_left
  intro I
  have hs1 : Measurable (fun ω ↦ ∑ j : Fin b, v ω (I j)) :=
    Finset.measurable_sum _ (fun j _ ↦ hv (I j))
  have hs2 : Measurable (fun ω ↦ ∑ i : Fin n, v ω i) :=
    Finset.measurable_sum _ (fun i _ ↦ hv i)
  exact (hs1.const_smul ((b : ℝ)⁻¹)).sub (hs2.const_smul ((n : ℝ)⁻¹))

/-- The conditional first moment is zero for arbitrary measurable vectors
chosen from the complete history, with genuine fresh independent samples. -/
theorem conditional_minibatch_centered (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Ω → Fin n → H} (hv : ∀ i, Measurable (fun ω ↦ v ω i)) (hb : 0 < b)
    (hint : Integrable (historyMinibatchError (b := b) v) (μ.prod (minibatchLaw n b))) :
    (μ.prod (minibatchLaw n b))[historyMinibatchError (b := b) v |
      mΩ.comap (Prod.fst : Ω × (Fin b → Fin n) → Ω)] =ᵐ[μ.prod (minibatchLaw n b)]
        fun _ ↦ (0 : H) := by
  have he := conditional_product_integral μ (minibatchLaw n b)
    (historyMinibatchError_measurable hv).stronglyMeasurable hint
  apply he.trans
  filter_upwards with a
  exact minibatch_centered_integral hb (v a.1)

/-- Exact conditional variance, rather than a variance assumption about an
iterate that may depend on a previously drawn estimator error. -/
theorem conditional_minibatch_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Ω → Fin n → H} (hv : ∀ i, Measurable (fun ω ↦ v ω i)) (hb : 0 < b)
    (hint : Integrable (fun a ↦ ‖historyMinibatchError (b := b) v a‖ ^ 2)
      (μ.prod (minibatchLaw n b))) :
    (μ.prod (minibatchLaw n b))[(fun a ↦ ‖historyMinibatchError (b := b) v a‖ ^ 2) |
      mΩ.comap (Prod.fst : Ω × (Fin b → Fin n) → Ω)] =ᵐ[μ.prod (minibatchLaw n b)]
        fun a ↦ (b : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ i, ‖v a.1 i‖ ^ 2 -
          ‖(n : ℝ)⁻¹ • ∑ i, v a.1 i‖ ^ 2) := by
  have he := conditional_product_integral μ (minibatchLaw n b)
    ((historyMinibatchError_measurable hv).norm.pow_const 2).stronglyMeasurable hint
  apply he.trans
  filter_upwards with a
  exact minibatch_variance_identity hb (v a.1)

/-- AS controls the conditional variance for two iterates selected from the
history before this minibatch is sampled. -/
theorem AveragedSmooth.conditional_minibatch_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Fin n → E → H} {s : Set E} {L : ℝ} (hG : AveragedSmooth G s L)
    {x y : Ω → E} (hx : ∀ ω, x ω ∈ s) (hy : ∀ ω, y ω ∈ s)
    (hv : ∀ i, Measurable (fun ω ↦ G i (x ω) - G i (y ω))) (hb : 0 < b)
    (hint : Integrable (fun a ↦ ‖historyMinibatchError (b := b)
      (fun ω i ↦ G i (x ω) - G i (y ω)) a‖ ^ 2) (μ.prod (minibatchLaw n b))) :
    ∀ᵐ a ∂μ.prod (minibatchLaw n b),
      ((μ.prod (minibatchLaw n b))[(fun a ↦ ‖historyMinibatchError (b := b)
        (fun ω i ↦ G i (x ω) - G i (y ω)) a‖ ^ 2) |
        mΩ.comap (Prod.fst : Ω × (Fin b → Fin n) → Ω)]) a ≤
        (L ^ 2 / b) * ‖x a.1 - y a.1‖ ^ 2 := by
  have he := conditional_product_integral μ (minibatchLaw n b)
    ((historyMinibatchError_measurable hv).norm.pow_const 2).stronglyMeasurable hint
  filter_upwards [he] with a ha
  rw [ha]
  have hh := hG.minibatch_variance_bound hb (hx a.1) (hy a.1)
  have hdiff : averageMap G (x a.1) - averageMap G (y a.1) =
      (n : ℝ)⁻¹ • ∑ i, (G i (x a.1) - G i (y a.1)) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  simpa only [historyMinibatchError, hdiff] using hh

end

end NCConcave16991
