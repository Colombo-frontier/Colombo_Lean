import Nonsmooth.VectorGaussianEnvelope

open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem potential_vector_weighted_hasFDerivAt (V : E → ℝ) (F : E → G)
    (x : E) (s : E →L[ℝ] ℝ) (L : E →L[ℝ] G)
    (hV : HasFDerivAt V s x) (hF : HasFDerivAt F L x) :
    HasFDerivAt (fun y => Real.exp (-V y) • F y)
      (Real.exp (-V x) • (L - s.smulRight (F x))) x := by
  convert! (hV.neg.exp).smul hF using 1
  ext v
  simp only [add_apply, smul_apply,
    neg_apply, Pi.neg_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply, smul_sub, smul_eq_mul, mul_neg,
    neg_smul, mul_smul, sub_eq_add_neg, smul_add, smul_neg]

/-- Multidimensional parameter differentiation of the actual weighted moment,
with a scalar coordinate integrated out and an explicit Gaussian envelope. -/
theorem potential_vector_moment_hasFDerivAt
    (V : E → ℝ → ℝ) (s : E → ℝ → E →L[ℝ] ℝ)
    (F : E → ℝ → G) (L : E → ℝ → E →L[ℝ] G) (t : E)
    (hV : Continuous (Function.uncurry V)) (hs : Continuous (Function.uncurry s))
    (hF : Continuous (Function.uncurry F)) (hL : Continuous (Function.uncurry L))
    (hdV : ∀ r x, HasFDerivAt (fun r => V r x) (s r x) r)
    (hdF : ∀ r x, HasFDerivAt (fun r => F r x) (L r x) r)
    {a B C D : ℝ} {m l : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hFb : ∀ x, ‖F t x‖ ≤ C * (1 + |x| ^ m))
    (hDb : ∀ r ∈ Metric.ball t 1, ∀ x,
      ‖L r x - (s r x).smulRight (F r x)‖ ≤ D * (1 + |x| ^ l)) :
    HasFDerivAt (fun r => ∫ x : ℝ, Real.exp (-V r x) • F r x)
      (∫ x : ℝ, Real.exp (-V t x) • (L t x - (s t x).smulRight (F t x))) t := by
  let W : E → ℝ → G := fun r x => Real.exp (-V r x) • F r x
  let W' : E → ℝ → E →L[ℝ] G := fun r x => Real.exp (-V r x) • (L r x - (s r x).smulRight (F r x))
  have hcW : Continuous (Function.uncurry W) := (Real.continuous_exp.comp hV.neg).smul hF
  have hcW' : Continuous (Function.uncurry W') :=
    (Real.continuous_exp.comp hV.neg).smul
      (hL.sub ((ContinuousLinearMap.smulRightL ℝ E G).continuous₂.comp₂ hs hF))
  have hpair (r : E) : Continuous (fun x : ℝ => (r, x)) := continuous_const.prodMk continuous_id
  have hm (r : E) : AEStronglyMeasurable (W r) := by
    simpa only [Function.uncurry, Function.comp_def] using (hcW.comp (hpair r)).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (W' t) := by
    simpa only [Function.uncurry, Function.comp_def] using (hcW'.comp (hpair t)).aestronglyMeasurable
  have hi : Integrable (W t) := potential_vector_weighted_integrable (V t) (F t) (hm t) ha
    (hVb t (by simp)) hFb
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F := W) (F' := W') (s := Metric.ball t 1)
    (bound := fun x => (Real.exp B * D) * (1 + |x| ^ l) * Real.exp (-a * x ^ 2))
    (Metric.ball_mem_nhds t zero_lt_one) (Eventually.of_forall hm) hi hm'
  · apply Eventually.of_forall
    intro x r hr
    exact potential_vector_weighted_bound (V r) (fun x => L r x - (s r x).smulRight (F r x))
      (hVb r hr) (hDb r hr) x
  · exact gaussian_polynomial_envelope_integrable ha (Real.exp B * D) l
  · apply Eventually.of_forall
    intro x r _
    exact potential_vector_weighted_hasFDerivAt (fun r => V r x) (fun r => F r x)
      r (s r x) (L r x) (hdV r x) (hdF r x)

theorem potential_vector_moment_continuousAt (V : E → ℝ → ℝ) (F : E → ℝ → G) (t : E)
    (hV : Continuous (Function.uncurry V)) (hF : Continuous (Function.uncurry F))
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ᶠ r in 𝓝 t, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hFb : ∀ᶠ r in 𝓝 t, ∀ x, ‖F r x‖ ≤ C * (1 + |x| ^ m)) :
    ContinuousAt (fun r => ∫ x : ℝ, Real.exp (-V r x) • F r x) t := by
  have hc : Continuous (Function.uncurry (fun r x => Real.exp (-V r x) • F r x)) :=
    (Real.continuous_exp.comp hV.neg).smul hF
  apply continuousAt_of_dominated
    (bound := fun x => (Real.exp B * C) * (1 + |x| ^ m) * Real.exp (-a * x ^ 2))
  · apply Eventually.of_forall
    intro r
    have hpair : Continuous (fun x : ℝ => (r, x)) := continuous_const.prodMk continuous_id
    simpa only [Function.uncurry, Function.comp_def] using (hc.comp hpair).aestronglyMeasurable
  · filter_upwards [hVb, hFb] with r hrV hrF
    exact Eventually.of_forall (potential_vector_weighted_bound (V r) (F r) hrV hrF)
  · exact gaussian_polynomial_envelope_integrable ha (Real.exp B * C) m
  · apply Eventually.of_forall
    intro x
    have hpair : Continuous (fun r : E => (r, x)) := continuous_id.prodMk continuous_const
    simpa only [Function.uncurry, Function.comp_def] using (hc.comp hpair).continuousAt

end
end Nonsmooth
