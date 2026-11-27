import Nonsmooth.VectorPotentialNormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem potential_negative_exp_integrable (U : ℝ → ℝ) (hU : Continuous U)
    {a B : ℝ} (ha : 0 < a) (hb : ∀ x, a * x ^ 2 - B ≤ U x) :
    Integrable (fun x : ℝ => Real.exp (-U x)) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => Real.exp (-U x) • (1 : ℝ)) := by
    simpa only [smul_eq_mul, mul_one, Function.comp_def, Pi.neg_apply] using
      (Real.continuous_exp.comp hU.neg).aestronglyMeasurable
  simpa only [smul_eq_mul, mul_one] using potential_vector_weighted_integrable U
    (fun _ => (1 : ℝ)) hm (C := 1) (m := 0) ha hb (fun _ => by norm_num)

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Differentiation of an actual normalized vector expectation. The
normalizing term appears as the product of the two actual expectations. -/
theorem potential_vector_expectation_hasFDerivAt
    (V : E → ℝ → ℝ) (s : E → ℝ → E →L[ℝ] ℝ)
    (F : E → ℝ → G) (L : E → ℝ → E →L[ℝ] G) (t : E)
    (hV : Continuous (Function.uncurry V)) (hs : Continuous (Function.uncurry s))
    (hF : Continuous (Function.uncurry F)) (hL : Continuous (Function.uncurry L))
    (hdV : ∀ r x, HasFDerivAt (fun r => V r x) (s r x) r)
    (hdF : ∀ r x, HasFDerivAt (fun r => F r x) (L r x) r)
    {a B C D J : ℝ} {m l n : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hFb : ∀ x, ‖F t x‖ ≤ C * (1 + |x| ^ m))
    (hDb : ∀ r ∈ Metric.ball t 1, ∀ x,
      ‖L r x - (s r x).smulRight (F r x)‖ ≤ D * (1 + |x| ^ l))
    (hsb : ∀ r ∈ Metric.ball t 1, ∀ x, ‖s r x‖ ≤ J * (1 + |x| ^ n)) :
    HasFDerivAt (fun r => ∫ x : ℝ, F r x ∂realDensityLaw (fun x => Real.exp (-V r x)))
      ((∫ x : ℝ, L t x - (s t x).smulRight (F t x) ∂realDensityLaw (fun x => Real.exp (-V t x))) +
        (∫ x : ℝ, s t x ∂realDensityLaw (fun x => Real.exp (-V t x))).smulRight
          (∫ x : ℝ, F t x ∂realDensityLaw (fun x => Real.exp (-V t x)))) t := by
  let Z := fun r => ∫ x : ℝ, Real.exp (-V r x)
  let M := fun r => ∫ x : ℝ, Real.exp (-V r x) • F r x
  let S := ∫ x : ℝ, Real.exp (-V t x) • s t x
  let N := ∫ x : ℝ, Real.exp (-V t x) • (L t x - (s t x).smulRight (F t x))
  have hVc (r : E) : Continuous (V r) := by
    have hp : Continuous (fun x : ℝ => (r, x)) := continuous_const.prodMk continuous_id
    simpa only [Function.uncurry, Function.comp_def] using hV.comp hp
  have hi (r : E) (hr : r ∈ Metric.ball t 1) : Integrable (fun x => Real.exp (-V r x)) :=
    potential_negative_exp_integrable (V r) (hVc r) ha (hVb r hr)
  have hit := hi t (by simp)
  have hz : Z t ≠ 0 := (integral_exp_pos hit).ne'
  have hZ : HasFDerivAt Z (-S) t := potential_partition_hasFDerivAt V s t hV hs hdV ha hVb hsb
  have hM : HasFDerivAt M N t := potential_vector_moment_hasFDerivAt V s F L t hV hs hF hL hdV hdF ha hVb hFb hDb
  have hInv := (hasDerivAt_inv hz).comp_hasFDerivAt t hZ
  have hNorm := hInv.smul hM
  have heq : (fun r => ∫ x : ℝ, F r x ∂realDensityLaw (fun x => Real.exp (-V r x))) =ᶠ[𝓝 t]
      fun r => (Z r)⁻¹ • M r := by
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact realDensityLaw_vector_integral _ (Real.continuous_exp.comp (hVc r).neg).measurable
      (hi r hr) (fun _ => (Real.exp_pos _).le) (F r)
  have hFinal := hNorm.congr_of_eventuallyEq heq
  have hwm : Measurable (fun x : ℝ => Real.exp (-V t x)) :=
    (Real.continuous_exp.comp (hVc t).neg).measurable
  have heN := realDensityLaw_vector_integral _ hwm hit (fun _ => (Real.exp_pos _).le)
    (fun x => L t x - (s t x).smulRight (F t x))
  have heS := realDensityLaw_vector_integral _ hwm hit (fun _ => (Real.exp_pos _).le) (s t)
  have heM := realDensityLaw_vector_integral _ hwm hit (fun _ => (Real.exp_pos _).le) (F t)
  rw [heN, heS, heM]
  convert! hFinal using 1
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply,
    neg_smul, smul_neg, neg_neg, smul_smul, smul_eq_mul, inv_pow, pow_two]
  simp only [Z, M, S, N]
  congr 1
  congr 1
  ring

end
end Nonsmooth
