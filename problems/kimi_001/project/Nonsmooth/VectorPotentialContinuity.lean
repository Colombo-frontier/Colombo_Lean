import Nonsmooth.VectorPotentialExpectation

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem potential_vector_expectation_continuousAt
    (V : E → ℝ → ℝ) (F : E → ℝ → G) (t : E)
    (hV : Continuous (Function.uncurry V)) (hF : Continuous (Function.uncurry F))
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hFb : ∀ r ∈ Metric.ball t 1, ∀ x, ‖F r x‖ ≤ C * (1 + |x| ^ m)) :
    ContinuousAt (fun r => ∫ x : ℝ, F r x ∂realDensityLaw (fun x => Real.exp (-V r x))) t := by
  let Z := fun r => ∫ x : ℝ, Real.exp (-V r x)
  let M := fun r => ∫ x : ℝ, Real.exp (-V r x) • F r x
  have hVe : ∀ᶠ r in 𝓝 t, ∀ x, a * x ^ 2 - B ≤ V r x := by
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact hVb r hr
  have hFe : ∀ᶠ r in 𝓝 t, ∀ x, ‖F r x‖ ≤ C * (1 + |x| ^ m) := by
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
    exact hFb r hr
  have hZ : ContinuousAt Z t := by
    simpa only [smul_eq_mul, mul_one] using potential_vector_moment_continuousAt V
      (fun _ _ => (1 : ℝ)) t hV continuous_const (C := 1) (m := 0) ha hVe
        (Eventually.of_forall (fun _ _ => by norm_num))
  have hM : ContinuousAt M t := potential_vector_moment_continuousAt V F t hV hF ha hVe hFe
  have hVc (r : E) : Continuous (V r) := by
    have hp : Continuous (fun x : ℝ => (r, x)) := continuous_const.prodMk continuous_id
    simpa only [Function.uncurry, Function.comp_def] using hV.comp hp
  have hi (r : E) (hr : r ∈ Metric.ball t 1) : Integrable (fun x => Real.exp (-V r x)) :=
    potential_negative_exp_integrable (V r) (hVc r) ha (hVb r hr)
  have hz : Z t ≠ 0 := (integral_exp_pos (hi t (by simp))).ne'
  apply ((hZ.inv₀ hz).smul hM).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with r hr
  exact realDensityLaw_vector_integral _ (Real.continuous_exp.comp (hVc r).neg).measurable
    (hi r hr) (fun _ => (Real.exp_pos _).le) (F r)

end
end Nonsmooth
