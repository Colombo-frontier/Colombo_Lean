import Nonsmooth.VectorGaussianEnvelope
import Nonsmooth.GaussianPolynomialEnvelope

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem potential_offset_weighted_bound (V F : ℝ → ℝ) {a B C : ℝ} {m : ℕ}
    (hV : ∀ x, a * x ^ 2 - B ≤ V x) (hF : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) (x : ℝ) :
    ‖F x * Real.exp (-V x)‖ ≤
      (Real.exp B * C) * (1 + |x| ^ m) * Real.exp (-a * x ^ 2) := by
  simpa only [smul_eq_mul, mul_comm] using potential_vector_weighted_bound V F hV
    (fun x => by simpa only [Real.norm_eq_abs] using hF x) x

theorem potential_offset_weighted_integrable (V F : ℝ → ℝ)
    (hm : AEStronglyMeasurable (fun x => F x * Real.exp (-V x)))
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hV : ∀ x, a * x ^ 2 - B ≤ V x) (hF : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) :
    Integrable (fun x => F x * Real.exp (-V x)) :=
  (gaussian_polynomial_envelope_integrable ha (Real.exp B * C) m).mono' hm
    (Eventually.of_forall (potential_offset_weighted_bound V F hV hF))

theorem potential_offset_moment_regular (V s F F' : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : Continuous (Function.uncurry V)) (hs : Continuous (Function.uncurry s))
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hdV : ∀ r x, HasDerivAt (fun r => V r x) (s r x) r)
    (hdF : ∀ r x, HasDerivAt (fun r => F r x) (F' r x) r)
    {a B C D : ℝ} {m l : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hFb : ∀ x, |F t x| ≤ C * (1 + |x| ^ m))
    (hDb : ∀ r ∈ Metric.ball t 1, ∀ x, |F' r x - F r x * s r x| ≤ D * (1 + |x| ^ l)) :
    PotentialMomentRegularAt V s F F' t := by
  have hp (r : ℝ) : Continuous (fun x : ℝ => (r, x)) := continuous_const.prodMk continuous_id
  have hmeas (r : ℝ) : AEStronglyMeasurable (fun x => F r x * Real.exp (-V r x)) :=
    ((hF.comp (hp r)).mul (Real.continuous_exp.comp (hV.comp (hp r)).neg)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (fun x => (F' t x - F t x * s t x) * Real.exp (-V t x)) :=
    (((hF'.comp (hp t)).sub ((hF.comp (hp t)).mul (hs.comp (hp t)))).mul
      (Real.continuous_exp.comp (hV.comp (hp t)).neg)).aestronglyMeasurable
  refine ⟨1, by norm_num, fun x => (Real.exp B * D) * (1 + |x| ^ l) * Real.exp (-a * x ^ 2),
    Eventually.of_forall hmeas,
    potential_offset_weighted_integrable (V t) (F t) (hmeas t) ha
      (hVb t (by simp)) hFb,
    hDmeas, gaussian_polynomial_envelope_integrable ha (Real.exp B * D) l, ?_⟩
  exact Eventually.of_forall (fun x r hr => ⟨hdV r x, hdF r x,
    potential_offset_weighted_bound (V r) (fun x => F' r x - F r x * s r x)
      (hVb r hr) (hDb r hr) x⟩)

theorem potential_offset_moment_continuous (V F : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : Continuous (Function.uncurry V)) (hF : Continuous (Function.uncurry F))
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ᶠ r in 𝓝 t, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hFb : ∀ᶠ r in 𝓝 t, ∀ x, |F r x| ≤ C * (1 + |x| ^ m)) :
    PotentialMomentContinuousAt V F t := by
  have hp (r : ℝ) : Continuous (fun x : ℝ => (r, x)) := continuous_const.prodMk continuous_id
  have hq (x : ℝ) : Continuous (fun r : ℝ => (r, x)) := continuous_id.prodMk continuous_const
  refine ⟨fun x => (Real.exp B * C) * (1 + |x| ^ m) * Real.exp (-a * x ^ 2),
    gaussian_polynomial_envelope_integrable ha (Real.exp B * C) m, ?_, ?_, ?_⟩
  · exact Eventually.of_forall (fun r =>
      ((hF.comp (hp r)).mul (Real.continuous_exp.comp (hV.comp (hp r)).neg)).aestronglyMeasurable)
  · filter_upwards [hVb, hFb] with r hrV hrF
    exact Eventually.of_forall (potential_offset_weighted_bound (V r) (F r) hrV hrF)
  · exact Eventually.of_forall (fun x =>
      ((hF.comp (hq x)).mul (Real.continuous_exp.comp (hV.comp (hq x)).neg)).continuousAt)

end
end Nonsmooth
