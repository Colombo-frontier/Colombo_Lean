import Bilevel.OuterDescent
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Expected outer descent and actual uniform output

The descent inequality is obtained from Primitive and integrated for actual
random iterates. Integrability and the estimator's MSE are explicit inputs;
the final stationarity inequality is derived, not assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.StochasticOuter

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Jensen's square inequality, proved by integrating a centered square. -/
theorem square_integral_le (f : Ω → ℝ) (hf : Integrable f ν)
    (hf2 : Integrable (fun ω => f ω ^ 2) ν) :
    (∫ ω, f ω ∂ν) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂ν := by
  let m := ∫ ω, f ω ∂ν
  have hid : (fun ω => (f ω - m) ^ 2) = fun ω => (f ω ^ 2 - (2 * m) * f ω) + m ^ 2 := by
    funext ω
    ring
  have hn : 0 ≤ ∫ ω, (f ω - m) ^ 2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  have ha : Integrable (fun ω => f ω ^ 2 - (2 * m) * f ω) ν := hf2.sub (hf.const_mul (2 * m))
  rw [hid, integral_add ha (integrable_const (m ^ 2)),
    integral_sub hf2 (hf.const_mul (2 * m)), integral_const_mul] at hn
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hn
  dsimp [m] at hn
  nlinarith

/-- A nonnegative function with an integrable square is integrable on a
probability space; no separate integrability premise is needed for the norm. -/
theorem integrable_of_integrable_sq (f : Ω → ℝ) (hn : ∀ ω, 0 ≤ f ω)
    (hf2 : Integrable (fun ω => f ω ^ 2) ν) : Integrable f ν := by
  have hm : AEStronglyMeasurable f ν := by
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable hf2.aestronglyMeasurable
    convert h using 1
    funext ω
    simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (hn ω)]
  apply ((integrable_const (1 : ℝ)).add hf2).mono' hm
  filter_upwards [] with ω
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (hn ω)]
  nlinarith [sq_nonneg (f ω - 1)]

def uniformLaw (n : ℕ) [NeZero n] : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure

instance uniformLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (uniformLaw n) := by
  unfold uniformLaw
  infer_instance

theorem uniform_integral (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    (∫ i, f i ∂uniformLaw n) = (∑ i, f i) / (n : ℝ) := by
  have hf : Integrable f (uniformLaw n) := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (Set.finite_univ) : IntegrableOn f Set.univ (uniformLaw n))
  rw [integral_fintype f hf]
  simp only [uniformLaw, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- The output law is an independent, genuinely uniform finite index times
the probability space carrying the adaptive algorithm. -/
def outputLaw (n : ℕ) [NeZero n] (ν : Measure Ω) : Measure (Fin n × Ω) :=
  (uniformLaw n).prod ν

instance outputLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (outputLaw n ν) := by
  unfold outputLaw
  infer_instance

def selected {E : Type*} (x : ℕ → Ω → E) {n : ℕ} (p : Fin n × Ω) : E := x p.1 p.2

theorem selected_measurable {E : Type*} [MeasurableSpace E] (x : ℕ → Ω → E)
    (n : ℕ) (hx : ∀ k < n, Measurable (x k)) :
    Measurable (selected x : Fin n × Ω → E) := by
  have h : Measurable (fun p : Ω × Fin n => x p.2 p.1) :=
    measurable_from_prod_countable (fun i : Fin n => hx i i.isLt)
  exact h.comp measurable_swap

omit [IsProbabilityMeasure ν] in
/-- Finite mixing preserves integrability without requiring pointwise measurable
versions of the individual integrable functions. -/
theorem integrable_uniform_output (n : ℕ) [NeZero n] (f : ℕ → Ω → ℝ)
    (hf : ∀ k < n, Integrable (f k) ν) :
    Integrable (fun p : Fin n × Ω => f p.1 p.2) (outputLaw n ν) := by
  classical
  have hi (i : Fin n) : Integrable (fun p : Fin n × Ω =>
      (if p.1 = i then (1 : ℝ) else 0) * f i p.2) (outputLaw n ν) := by
    have hd : Integrable (fun j : Fin n => if j = i then (1 : ℝ) else 0) (uniformLaw n) := by
      simpa only [integrableOn_univ] using
        (IntegrableOn.of_finite Set.finite_univ : IntegrableOn
          (fun j : Fin n => if j = i then (1 : ℝ) else 0) Set.univ (uniformLaw n))
    exact hd.mul_prod (hf i i.isLt)
  have hs := integrable_finset_sum Finset.univ (fun i _ => hi i)
  convert hs using 1
  funext p
  simp

theorem uniform_output_integral (n : ℕ) [NeZero n] (f : ℕ → Ω → ℝ)
    (hf : Integrable (fun p : Fin n × Ω => f p.1 p.2) (outputLaw n ν)) :
    (∫ p : Fin n × Ω, f p.1 p.2 ∂outputLaw n ν) =
      (∑ i ∈ Finset.range n, ∫ ω, f i ω ∂ν) / (n : ℝ) := by
  rw [outputLaw, integral_prod _ hf, uniform_integral]
  simp only [Prod.fst, Prod.snd]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => ∫ ω, f i ω ∂ν) n

end Bilevel.StochasticOuter

namespace Bilevel.Model.Primitive

variable {X Y Ω : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

omit [IsProbabilityMeasure ν] in
theorem expected_outer_step (r : P.Response) (x xn G : Ω → X) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ)
    (hstep : ∀ᵐ ω ∂ν, xn ω = x ω - Λ⁻¹ • G ω)
    (hx : Integrable (fun ω => P.hyperobjective r (x ω)) ν)
    (hxn : Integrable (fun ω => P.hyperobjective r (xn ω)) ν)
    (hg : Integrable (fun ω => ‖gradient (P.hyperobjective r) (x ω)‖ ^ 2) ν)
    (he : Integrable (fun ω => ‖G ω - gradient (P.hyperobjective r) (x ω)‖ ^ 2) ν) :
    (∫ ω, P.hyperobjective r (xn ω) ∂ν) ≤ (∫ ω, P.hyperobjective r (x ω) ∂ν) -
      (∫ ω, ‖gradient (P.hyperobjective r) (x ω)‖ ^ 2 ∂ν) / (2 * Λ) +
      (∫ ω, ‖G ω - gradient (P.hyperobjective r) (x ω)‖ ^ 2 ∂ν) / (2 * Λ) := by
  have hb : ∀ᵐ ω ∂ν, P.hyperobjective r (xn ω) ≤ P.hyperobjective r (x ω) -
      ‖gradient (P.hyperobjective r) (x ω)‖ ^ 2 / (2 * Λ) +
      ‖G ω - gradient (P.hyperobjective r) (x ω)‖ ^ 2 / (2 * Λ) := by
    filter_upwards [hstep] with ω hω
    rw [hω]
    exact P.outer_inexact_descent r (x ω) (G ω) Λ hΛpos hΛ
  have h := integral_mono_ae hxn ((hx.sub (hg.div_const _)).add (he.div_const _)) hb
  have hmain : Integrable (fun ω => P.hyperobjective r (x ω) -
      ‖gradient (P.hyperobjective r) (x ω)‖ ^ 2 / (2 * Λ)) ν := hx.sub (hg.div_const (2 * Λ))
  simp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_add hmain (he.div_const (2 * Λ)),
    integral_sub hx (hg.div_const (2 * Λ)), integral_div, integral_div] at h
  exact h

/-- Expected squared gradients are bounded by actual integrated descent and MSE. -/
theorem expected_average_gradient_sq (r : P.Response) (x G : ℕ → Ω → X) (x₀ : X)
    {Δ δ : ℝ} (gap : P.GapCertificate r x₀ Δ) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ) (n : ℕ) (hn : 0 < n)
    (hinit : ∀ᵐ ω ∂ν, x 0 ω = x₀)
    (hstep : ∀ k < n, ∀ᵐ ω ∂ν, x (k + 1) ω = x k ω - Λ⁻¹ • G k ω)
    (hx : ∀ k ≤ n, Integrable (fun ω => P.hyperobjective r (x k ω)) ν)
    (hg : ∀ k < n, Integrable (fun ω => ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2) ν)
    (he : ∀ k < n, Integrable (fun ω => ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2) ν)
    (hmse : ∀ k < n, (∫ ω, ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2 ∂ν) ≤ δ) :
    (∑ k ∈ Finset.range n, ∫ ω, ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2 ∂ν) / (n : ℝ) ≤
      2 * Λ * Δ / n + δ := by
  have hstart : (∫ ω, P.hyperobjective r (x 0 ω) ∂ν) = P.hyperobjective r x₀ := by
    calc
      _ = ∫ _ω : Ω, P.hyperobjective r x₀ ∂ν := integral_congr_ae (hinit.mono (fun _ h => congrArg _ h))
      _ = _ := by simp
  have hfloor : gap.floor ≤ ∫ ω, P.hyperobjective r (x n ω) ∂ν := by
    have h := integral_mono_ae (integrable_const gap.floor) (hx n le_rfl)
      (Filter.Eventually.of_forall (fun ω => gap.lower_bound (x n ω)))
    simpa using h
  apply Descent.averaged_gradient_sq_of_uniform_error
    (fun k => ∫ ω, P.hyperobjective r (x k ω) ∂ν)
    (fun k => ∫ ω, ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2 ∂ν)
    (fun k => ∫ ω, ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2 ∂ν)
    Λ Δ δ n hn hΛpos
  · rw [hstart]
    linarith [gap.gap]
  · intro k hk
    exact P.expected_outer_step r (x k) (x (k + 1)) (G k) Λ hΛpos hΛ (hstep k hk)
      (hx k hk.le) (hx (k + 1) hk) (hg k hk) (he k hk)
  · exact hmse

/-- The output is sampled under the independent uniform-index probability
law, and its actual expected squared hypergradient obeys the telescoped bound. -/
theorem expected_uniform_gradient_sq (r : P.Response) (x G : ℕ → Ω → X) (x₀ : X)
    {Δ δ : ℝ} (gap : P.GapCertificate r x₀ Δ) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ) (n : ℕ) [NeZero n]
    (hinit : ∀ᵐ ω ∂ν, x 0 ω = x₀)
    (hstep : ∀ k < n, ∀ᵐ ω ∂ν, x (k + 1) ω = x k ω - Λ⁻¹ • G k ω)
    (hx : ∀ k ≤ n, Integrable (fun ω => P.hyperobjective r (x k ω)) ν)
    (hg : ∀ k < n, Integrable (fun ω => ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2) ν)
    (he : ∀ k < n, Integrable (fun ω => ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2) ν)
    (hmse : ∀ k < n, (∫ ω, ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2 ∂ν) ≤ δ) :
    (∫ p : Fin n × Ω, ‖gradient (P.hyperobjective r) (StochasticOuter.selected x p)‖ ^ 2
      ∂StochasticOuter.outputLaw n ν) ≤ 2 * Λ * Δ / n + δ := by
  have hprod := StochasticOuter.integrable_uniform_output n
    (fun k ω => ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2) hg
  rw [show (fun p : Fin n × Ω =>
      ‖gradient (P.hyperobjective r) (StochasticOuter.selected x p)‖ ^ 2) =
      (fun p : Fin n × Ω => ‖gradient (P.hyperobjective r) (x p.1 p.2)‖ ^ 2) from rfl,
    StochasticOuter.uniform_output_integral n
      (fun k ω => ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2) hprod]
  exact P.expected_average_gradient_sq r x G x₀ gap Λ hΛpos hΛ n
    (Nat.pos_of_neZero n) hinit hstep hx hg he hmse

/-- An actual uniform random iterate meets the expected-gradient-norm target
after the prescribed finite number of inexact gradient steps. -/
theorem expected_uniform_gradient_norm (r : P.Response) (x G : ℕ → Ω → X) (x₀ : X)
    {Δ ε : ℝ} (gap : P.GapCertificate r x₀ Δ) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ) (n : ℕ) [NeZero n]
    (hε : 0 ≤ ε) (hcount : 4 * Λ * Δ ≤ (n : ℝ) * ε ^ 2)
    (hinit : ∀ᵐ ω ∂ν, x 0 ω = x₀)
    (hstep : ∀ k < n, ∀ᵐ ω ∂ν, x (k + 1) ω = x k ω - Λ⁻¹ • G k ω)
    (hx : ∀ k ≤ n, Integrable (fun ω => P.hyperobjective r (x k ω)) ν)
    (hg : ∀ k < n, Integrable (fun ω => ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2) ν)
    (he : ∀ k < n, Integrable (fun ω => ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2) ν)
    (hmse : ∀ k < n, (∫ ω, ‖G k ω - gradient (P.hyperobjective r) (x k ω)‖ ^ 2 ∂ν) ≤ ε ^ 2 / 16) :
    (∫ p : Fin n × Ω, ‖gradient (P.hyperobjective r) (StochasticOuter.selected x p)‖
      ∂StochasticOuter.outputLaw n ν) ≤ ε := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_neZero n)
  have hbudget : 2 * Λ * Δ / n ≤ ε ^ 2 / 2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hsq := P.expected_uniform_gradient_sq r x G x₀ gap Λ hΛpos hΛ n
    hinit hstep hx hg he hmse
  have hprod := StochasticOuter.integrable_uniform_output n
    (fun k ω => ‖gradient (P.hyperobjective r) (x k ω)‖ ^ 2) hg
  have hint := StochasticOuter.integrable_of_integrable_sq
    (fun p : Fin n × Ω => ‖gradient (P.hyperobjective r) (StochasticOuter.selected x p)‖)
    (fun _ => norm_nonneg _) hprod
  have hj := StochasticOuter.square_integral_le _ hint hprod
  nlinarith [sq_nonneg ε]

end Bilevel.Model.Primitive
