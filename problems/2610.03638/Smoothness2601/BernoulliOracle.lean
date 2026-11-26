import Bilevel.BernoulliOracle
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The manuscript's two-loss Bernoulli oracle

This file verifies the actual probability measure, Bochner mean, squared-error
integral, and sample-potential gradient in equations `new-q`--`new-oracle` of
2601.tex (lines 1109--1138). Its probability is precisely `B² / σ²`, unlike
the auxiliary normalization `B² / (σ² + B²)` used in the imported library.

Freshness is represented by a constant Markov kernel, whose coin law is
independent of the entire preceding history. The moment statements hold at
every history, even when both gradient fields depend on that history.

The concrete sine-lift derivative and its global signal bound are separate
obligations. No smoothness or convexity of individual sample losses is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Smoothness2601.BernoulliOracle

abbrev law := Bilevel.BernoulliOracle.law
abbrev response := @Bilevel.BernoulliOracle.sample

/-- The exact reveal probability in the manuscript, with `B = C_* s h`. -/
def revealProbability (B σ : ℝ) : ℝ := B ^ 2 / σ ^ 2

theorem revealProbability_pos {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    0 < revealProbability B σ := by
  unfold revealProbability
  positivity

theorem revealProbability_le_one {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ)
    (hsmall : B ≤ σ) : revealProbability B σ ≤ 1 := by
  unfold revealProbability
  apply (div_le_one (sq_pos_of_pos hσ)).mpr
  nlinarith

theorem revealProbability_lt_one {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ)
    (hsmall : B < σ) : revealProbability B σ < 1 := by
  unfold revealProbability
  apply (div_lt_one (sq_pos_of_pos hσ)).mpr
  nlinarith

theorem revealProbability_source_formula (C s h σ : ℝ) :
    revealProbability (C * s * h) σ = C ^ 2 * s ^ 2 * h ^ 2 / σ ^ 2 := by
  simp only [revealProbability, mul_pow]

theorem revealProbability_variance {B σ : ℝ} (hB : 0 < B) :
    ((revealProbability B σ)⁻¹ - 1) * B ^ 2 = σ ^ 2 - B ^ 2 := by
  unfold revealProbability
  rw [inv_div]
  field_simp

section Moments

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem response_mean {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (base signal : E) :
    (∫ z, response q base signal z ∂law q hq1) = base + signal :=
  Bilevel.BernoulliOracle.sample_mean q hq0 hq1 base signal

omit [CompleteSpace E] in
theorem response_variance {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (base signal : E) :
    (∫ z, ‖response q base signal z - (base + signal)‖ ^ 2 ∂law q hq1) =
      (q⁻¹ - 1) * ‖signal‖ ^ 2 :=
  Bilevel.BernoulliOracle.sample_variance q hq0 hq1 base signal

omit [CompleteSpace E] in
/-- A global signal bound implies the original variance budget for this exact
choice of reveal probability. The slightly sharper result subtracts `B²`. -/
theorem response_variance_le {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hsmall : B ≤ σ) (base signal : E) (henv : ‖signal‖ ≤ B) :
    (∫ z, ‖response (revealProbability B σ) base signal z - (base + signal)‖ ^ 2
      ∂law (revealProbability B σ) (revealProbability_le_one hB.le hσ hsmall)) ≤
      σ ^ 2 - B ^ 2 := by
  rw [response_variance (revealProbability_pos hB hσ)]
  have hsq : ‖signal‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg signal]
  have hcoeff : 0 ≤ (revealProbability B σ)⁻¹ - 1 := by
    have hq0 := revealProbability_pos hB hσ
    have hq1 := revealProbability_le_one hB.le hσ hsmall
    have hi : 1 ≤ (revealProbability B σ)⁻¹ := (one_le_inv₀ hq0).2 hq1
    linarith
  calc
    _ ≤ ((revealProbability B σ)⁻¹ - 1) * B ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoeff
    _ = _ := revealProbability_variance hB

/-- Global unbiasedness and bounded variance, pointwise on the entire query
domain `X`; in particular no neighborhood of the inner solution is imposed. -/
theorem globally_valid {X : Type*} {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hsmall : B ≤ σ) (base signal : X → E) (henv : ∀ x, ‖signal x‖ ≤ B) :
    ∀ x,
      (∫ z, response (revealProbability B σ) (base x) (signal x) z
        ∂law (revealProbability B σ) (revealProbability_le_one hB.le hσ hsmall)) =
          base x + signal x ∧
      (∫ z, ‖response (revealProbability B σ) (base x) (signal x) z -
        (base x + signal x)‖ ^ 2
        ∂law (revealProbability B σ) (revealProbability_le_one hB.le hσ hsmall)) ≤
          σ ^ 2 := by
  intro x
  constructor
  · exact response_mean (revealProbability_pos hB hσ) _ _ _
  · exact (response_variance_le hB hσ hsmall _ _ (henv x)).trans
      (sub_le_self _ (sq_nonneg B))

end Moments

section SamplePotentials

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The two scalar functions are fixed before sampling the Boolean coin. -/
def sampleLoss (q : ℝ) (base signal : V → ℝ) (z : Bool) (x : V) : ℝ :=
  base x + (if z then q⁻¹ else 0) * signal x

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] in
theorem sampleLoss_false (q : ℝ) (base signal : V → ℝ) :
    sampleLoss q base signal false = base := by
  funext x
  simp [sampleLoss]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] in
theorem sampleLoss_true (q : ℝ) (base signal : V → ℝ) :
    sampleLoss q base signal true = fun x => base x + q⁻¹ * signal x := by
  funext x
  simp [sampleLoss]

theorem sampleLoss_hasGradient {base signal : V → ℝ} {db ds x : V}
    (hbase : HasGradientAt base db x) (hsignal : HasGradientAt signal ds x)
    (q : ℝ) (z : Bool) :
    HasGradientAt (sampleLoss q base signal z) (response q db ds z) x := by
  simpa only [sampleLoss, Bilevel.BernoulliOracle.sample, smul_eq_mul] using
    Bilevel.BernoulliOracle.sample_hasGradient hbase hsignal q z

/-- An oracle sampling the actual gradients of the two fixed losses has the
actual population gradient as mean, at every query in the entire space. -/
theorem sampleLoss_gradients_valid {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hsmall : B ≤ σ) (base signal : V → ℝ) (db ds : V → V)
    (hbase : ∀ x, HasGradientAt base (db x) x)
    (hsignal : ∀ x, HasGradientAt signal (ds x) x)
    (henv : ∀ x, ‖ds x‖ ≤ B) (x : V) :
    (∫ z, gradient (sampleLoss (revealProbability B σ) base signal z) x
      ∂law (revealProbability B σ) (revealProbability_le_one hB.le hσ hsmall)) =
        gradient (fun w => base w + signal w) x ∧
    (∫ z, ‖gradient (sampleLoss (revealProbability B σ) base signal z) x -
      gradient (fun w => base w + signal w) x‖ ^ 2
      ∂law (revealProbability B σ) (revealProbability_le_one hB.le hσ hsmall)) ≤
        σ ^ 2 := by
  have hpop : gradient (fun w => base w + signal w) x = db x + ds x := by
    simpa [Bilevel.BernoulliOracle.sample] using
      (Bilevel.BernoulliOracle.sample_hasGradient (hbase x) (hsignal x) 1 true).gradient
  simp_rw [(sampleLoss_hasGradient (hbase x) (hsignal x) _ _).gradient, hpop]
  exact globally_valid hB hσ hsmall db ds henv x

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] in
/-- With the sine signal substituted, these are exactly the sample losses
displayed in the source. This is an identity, not a derivative assumption. -/
theorem sine_sampleLoss_formula (q m A b h : ℝ) (lower frontier : V → ℝ)
    (z : Bool) (x : V) :
    sampleLoss q (fun w => m / 2 * (lower w) ^ 2)
      (fun w => -(m * (A / b) * h * frontier w * Real.sin (lower w / h))) z x =
    m / 2 * (lower x) ^ 2 -
      (if z then q⁻¹ else 0) * m * (A / b) * h * frontier x *
        Real.sin (lower x / h) := by
  unfold sampleLoss
  ring

end SamplePotentials

section Freshness

variable {H E : Type*} [MeasurableSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Every history receives exactly the same independent coin law. -/
def freshCoin (q : ℝ) (hq1 : q ≤ 1) : Kernel H Bool := Kernel.const H (law q hq1)

instance freshCoin_isMarkov (q : ℝ) (hq1 : q ≤ 1) :
    IsMarkovKernel (freshCoin (H := H) q hq1) := by
  unfold freshCoin
  infer_instance

theorem freshCoin_apply (q : ℝ) (hq1 : q ≤ 1) (history : H) :
    freshCoin q hq1 history = law q hq1 := rfl

/-- Conditional on any preceding history, an adaptive response has precisely
the population mean. Neither `base` nor `signal` must be constant in history. -/
theorem fresh_response_mean {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (base signal : H → E) (history : H) :
    (∫ z, response q (base history) (signal history) z ∂freshCoin q hq1 history) =
      base history + signal history := response_mean hq0 hq1 _ _

omit [CompleteSpace E] in
theorem fresh_response_variance {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (base signal : H → E) (history : H) :
    (∫ z, ‖response q (base history) (signal history) z -
      (base history + signal history)‖ ^ 2 ∂freshCoin q hq1 history) =
      (q⁻¹ - 1) * ‖signal history‖ ^ 2 := response_variance hq0 hq1 _ _

end Freshness

end Smoothness2601.BernoulliOracle
