import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The conservative Bernoulli oracle: one-call laws

This module formalizes the actual two-point probability measure, its vector mean,
and its mean-square error. It applies pointwise to the sample-gradient formulas
in `lb:eq:sample-potential` and `sg:eq:oracle` of 0113.tex. The potential being
differentiable, its global envelope, and adaptation/freshness are separate
obligations; this file does not assert the manuscript's minimax theorem.
-/

noncomputable section
open MeasureTheory

namespace Bilevel.BernoulliOracle

/-- The genuine Bernoulli probability measure, including the endpoint `p = 1`. -/
def law (p : ℝ) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp)).toMeasure

instance law_isProbability (p : ℝ) (hp : p ≤ 1) : IsProbabilityMeasure (law p hp) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.bernoulli (ENNReal.ofReal p) _).toMeasure)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → E) :
    (∫ b, f b ∂law p hp1) = (1 - p) • f false + p • f true := by
  rw [law, PMF.integral_eq_sum]
  simp [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr hp1), hp0, add_comm]

/-- Response from the inactive gradient plus the activated informative gradient. -/
def sample (p : ℝ) (base signal : E) (b : Bool) : E :=
  base + (if b then p⁻¹ else 0) • signal

/-- Each oracle response is the actual gradient of its scalar sample potential,
provided the inactive and informative potentials have the stated gradients. -/
theorem sample_hasGradient
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {base signal : V → ℝ} {db ds x : V}
    (hbase : HasGradientAt base db x) (hsignal : HasGradientAt signal ds x)
    (p : ℝ) (b : Bool) :
    HasGradientAt (fun y => sample p (base y) (signal y) b) (sample p db ds b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hf := hbase.hasFDerivAt.add
    (hsignal.hasFDerivAt.const_smul (if b then p⁻¹ else 0))
  cases b <;> simpa [sample] using hf

theorem sample_mean (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (base signal : E) :
    (∫ b, sample p base signal b ∂law p hp1) = base + signal := by
  rw [integral_law p hp0.le hp1]
  simp only [sample, Bool.false_eq_true, ↓reduceIte, zero_smul, add_zero,
    smul_add, smul_smul]
  rw [mul_inv_cancel₀ hp0.ne']
  module

omit [CompleteSpace E] in
theorem sample_error_false (p : ℝ) (base signal : E) :
    sample p base signal false - (base + signal) = -signal := by
  simp [sample]

omit [CompleteSpace E] in
theorem sample_error_true (p : ℝ) (base signal : E) :
    sample p base signal true - (base + signal) = (p⁻¹ - 1) • signal := by
  simp only [sample, ↓reduceIte]
  module

omit [CompleteSpace E] in
theorem sample_variance (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (base signal : E) :
    (∫ b, ‖sample p base signal b - (base + signal)‖ ^ 2 ∂law p hp1) =
      (p⁻¹ - 1) * ‖signal‖ ^ 2 := by
  rw [integral_law p hp0.le hp1]
  simp only [sample_error_false, sample_error_true, norm_neg, norm_smul,
    Real.norm_eq_abs, smul_eq_mul, mul_pow, sq_abs]
  field_simp
  ring

/-- Revelation probability chosen from the global signal and variance budgets. -/
def probability (B σ : ℝ) : ℝ := B ^ 2 / (σ ^ 2 + B ^ 2)

theorem probability_pos {B σ : ℝ} (hB : 0 < B) : 0 < probability B σ := by
  unfold probability
  positivity

theorem probability_le_one {B σ : ℝ} (hB : 0 < B) : probability B σ ≤ 1 := by
  unfold probability
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg σ]

theorem inverse_probability {B σ : ℝ} (hB : 0 < B) :
    (probability B σ)⁻¹ = 1 + σ ^ 2 / B ^ 2 := by
  unfold probability
  field_simp
  ring

theorem probability_variance {B σ : ℝ} (hB : 0 < B) :
    ((probability B σ)⁻¹ - 1) * B ^ 2 = σ ^ 2 := by
  rw [inverse_probability hB]
  field_simp

omit [CompleteSpace E] in
theorem bounded_variance {B σ : ℝ} (hB : 0 < B) (base signal : E)
    (henv : ‖signal‖ ≤ B) :
    (∫ b, ‖sample (probability B σ) base signal b - (base + signal)‖ ^ 2
      ∂law (probability B σ) (probability_le_one hB)) ≤ σ ^ 2 := by
  rw [sample_variance _ (probability_pos hB)]
  have hsq : ‖signal‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg signal]
  have hcoeff : 0 ≤ (probability B σ)⁻¹ - 1 := by
    rw [inverse_probability hB]
    have : 0 ≤ σ ^ 2 / B ^ 2 := by positivity
    linarith
  calc
    _ ≤ ((probability B σ)⁻¹ - 1) * B ^ 2 := mul_le_mul_of_nonneg_left hsq hcoeff
    _ = _ := probability_variance hB

/-- The scalar final step of `sg:thm:lower`.
`testing` and `activation` must be supplied by an independently proved
stopped-transcript coupling and predictable Bernoulli counting argument. -/
theorem expected_queries_from_testing
    {p γ risk survival queries : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    (testing : γ * survival ≤ risk) (activation : 1 - survival ≤ p * queries)
    (accuracy : risk ≤ γ / 8) : 7 / (8 * p) ≤ queries := by
  apply (div_le_iff₀ (by positivity : 0 < 8 * p)).mpr
  have hs : survival ≤ (1 : ℝ) / 8 := by nlinarith
  nlinarith

end Bilevel.BernoulliOracle
