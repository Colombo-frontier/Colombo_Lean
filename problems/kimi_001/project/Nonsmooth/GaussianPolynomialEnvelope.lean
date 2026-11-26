import Nonsmooth.DominatedPotentialContinuity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem gaussian_polynomial_envelope_integrable {a : ℝ} (ha : 0 < a) (C : ℝ) (m : ℕ) :
    Integrable (fun x : ℝ => C * (1 + |x| ^ m) * Real.exp (-a * x ^ 2)) := by
  have h0 : Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) := integrable_exp_neg_mul_sq ha
  have hm : Integrable (fun x : ℝ => x ^ m * Real.exp (-a * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq ha
      (show (-1 : ℝ) < (m : ℝ) from lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m))
  have hma : Integrable (fun x : ℝ => |x| ^ m * Real.exp (-a * x ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using hm.norm
  convert! (h0.add hma).const_mul C using 1
  funext x
  simp only [Pi.add_apply]
  ring

theorem potential_weighted_polynomial_bound (V F : ℝ → ℝ) {a C : ℝ} {m : ℕ}
    (hV : ∀ x, a * x ^ 2 ≤ V x) (hF : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) (x : ℝ) :
    ‖F x * Real.exp (-V x)‖ ≤ C * (1 + |x| ^ m) * Real.exp (-a * x ^ 2) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-V x) ≤ Real.exp (-a * x ^ 2) :=
    Real.exp_le_exp.mpr (by linarith [hV x])
  exact mul_le_mul (hF x) he (Real.exp_pos _).le
    ((abs_nonneg (F x)).trans (hF x))

theorem potential_weighted_polynomial_integrable (V F : ℝ → ℝ)
    (hm : AEStronglyMeasurable (fun x => F x * Real.exp (-V x)))
    {a C : ℝ} {m : ℕ} (ha : 0 < a)
    (hV : ∀ x, a * x ^ 2 ≤ V x) (hF : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) :
    Integrable (fun x => F x * Real.exp (-V x)) :=
  (gaussian_polynomial_envelope_integrable ha C m).mono' hm
    (Eventually.of_forall (potential_weighted_polynomial_bound V F hV hF))

theorem potential_polynomial_moment_continuous (V F : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : Continuous (Function.uncurry V)) (hF : Continuous (Function.uncurry F))
    {a C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ᶠ r in 𝓝 t, ∀ x, a * x ^ 2 ≤ V r x)
    (hFb : ∀ᶠ r in 𝓝 t, ∀ x, |F r x| ≤ C * (1 + |x| ^ m)) :
    PotentialMomentContinuousAt V F t := by
  refine ⟨fun x => C * (1 + |x| ^ m) * Real.exp (-a * x ^ 2),
    gaussian_polynomial_envelope_integrable ha C m, ?_, ?_, ?_⟩
  · apply Eventually.of_forall
    intro r
    have hc : Continuous (fun x => F r x * Real.exp (-V r x)) :=
      (hF.comp (continuous_const.prodMk continuous_id)).mul
        (Real.continuous_exp.comp (hV.comp (continuous_const.prodMk continuous_id)).neg)
    exact hc.aestronglyMeasurable
  · filter_upwards [hVb, hFb] with r hrV hrF
    exact Eventually.of_forall (potential_weighted_polynomial_bound (V r) (F r) hrV hrF)
  · apply Eventually.of_forall
    intro x
    exact ((hF.comp (continuous_id.prodMk continuous_const)).mul
      (Real.continuous_exp.comp (hV.comp (continuous_id.prodMk continuous_const)).neg)).continuousAt

theorem potential_polynomial_moment_regular (V s F F' : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : Continuous (Function.uncurry V)) (hs : Continuous (Function.uncurry s))
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hdV : ∀ r x, HasDerivAt (fun r => V r x) (s r x) r)
    (hdF : ∀ r x, HasDerivAt (fun r => F r x) (F' r x) r)
    {a C D : ℝ} {m l : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 ≤ V r x)
    (hFb : ∀ x, |F t x| ≤ C * (1 + |x| ^ m))
    (hDb : ∀ r ∈ Metric.ball t 1, ∀ x, |F' r x - F r x * s r x| ≤ D * (1 + |x| ^ l)) :
    PotentialMomentRegularAt V s F F' t := by
  have hmeas (r : ℝ) : AEStronglyMeasurable (fun x => F r x * Real.exp (-V r x)) :=
    ((hF.comp (continuous_const.prodMk continuous_id)).mul
      (Real.continuous_exp.comp (hV.comp (continuous_const.prodMk continuous_id)).neg)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (fun x => (F' t x - F t x * s t x) * Real.exp (-V t x)) :=
    (((hF'.comp (continuous_const.prodMk continuous_id)).sub
      ((hF.comp (continuous_const.prodMk continuous_id)).mul
        (hs.comp (continuous_const.prodMk continuous_id)))).mul
      (Real.continuous_exp.comp (hV.comp (continuous_const.prodMk continuous_id)).neg)).aestronglyMeasurable
  refine ⟨1, by norm_num, fun x => D * (1 + |x| ^ l) * Real.exp (-a * x ^ 2),
    Eventually.of_forall hmeas,
    potential_weighted_polynomial_integrable (V t) (F t) (hmeas t) ha
      (hVb t (by simp)) hFb,
    hDmeas, gaussian_polynomial_envelope_integrable ha D l, ?_⟩
  apply Eventually.of_forall
  intro x r hr
  exact ⟨hdV r x, hdF r x,
    potential_weighted_polynomial_bound (V r) (fun x => F' r x - F r x * s r x)
      (hVb r hr) (hDb r hr) x⟩

end
end Nonsmooth
