import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Bernoulli erasure oracle

An actual two-point probability law, its unbiased reply and exact centered
real `p`-moment, and the probability of a finite independent erasure sequence.
This module does not define a general adaptive oracle algorithm.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace HeavyTail

noncomputable def erasureCoin (u : ℝ) (hu : u ≤ 1) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal u) (ENNReal.ofReal_le_one.mpr hu)

/-- `true` is the erasure outcome; a nonerased reply is importance weighted. -/
noncomputable def erasureReply (u g : ℝ) (b : Bool) : ℝ := if b then 0 else g / (1 - u)

theorem erasure_expectation_formula {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (f : Bool → ℝ) :
    (∫ b, f b ∂(erasureCoin u hu1).toMeasure) =
      u * f true + (1 - u) * f false := by
  rw [PMF.integral_eq_sum]
  simp only [erasureCoin, PMF.bernoulli_apply, Fintype.sum_bool, Bool.cond_false,
    Bool.cond_true, smul_eq_mul]
  rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr hu1) (by simp),
    ENNReal.toReal_one, ENNReal.toReal_ofReal hu0]

theorem erasure_unbiased {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (g : ℝ) :
    (∫ b, erasureReply u g b ∂(erasureCoin u hu1.le).toMeasure) = g := by
  rw [erasure_expectation_formula hu0]
  simp only [erasureReply, Bool.false_eq_true, if_false, if_true, mul_zero, zero_add]
  field_simp [ne_of_gt (sub_pos.mpr hu1)]

/-- Exact centered moment of the concrete importance-weighted erasure law. -/
theorem erasure_centered_moment {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (g p : ℝ) :
    (∫ b, |erasureReply u g b - g| ^ p ∂(erasureCoin u hu1.le).toMeasure) =
      |g| ^ p * (u + u ^ p / (1 - u) ^ (p - 1)) := by
  have hq : 0 < 1 - u := sub_pos.mpr hu1
  have hqne : 1 - u ≠ 0 := ne_of_gt hq
  have habs : |g / (1 - u) - g| = |g| * u / (1 - u) := by
    have hid : g / (1 - u) - g = g * u / (1 - u) := by field_simp; ring
    rw [hid, abs_div, abs_mul, abs_of_pos hu0, abs_of_pos hq]
  rw [erasure_expectation_formula hu0.le]
  simp only [erasureReply, Bool.false_eq_true, if_false, if_true, zero_sub, abs_neg]
  rw [habs, Real.div_rpow (mul_nonneg (abs_nonneg g) hu0.le) hq.le,
    Real.mul_rpow (abs_nonneg g) hu0.le, Real.rpow_sub_one hqne]
  have hpq : (1 - u) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hq p)
  field_simp
  <;> ring

/-- The product sample space contains independent copies of the actual coin. -/
noncomputable def erasureSequenceLaw (u : ℝ) (hu : u ≤ 1) (T : ℕ) :
    Measure (Fin T → Bool) := Measure.pi (fun _ ↦ (erasureCoin u hu).toMeasure)

theorem all_erased_probability {u : ℝ} (hu : u ≤ 1) (T : ℕ) :
    erasureSequenceLaw u hu T {b | ∀ i, b i = true} = (ENNReal.ofReal u) ^ T := by
  have hs : {b : Fin T → Bool | ∀ i, b i = true} =
      Set.univ.pi (fun _ : Fin T ↦ ({true} : Set Bool)) := by
    ext b
    simp
  rw [hs, erasureSequenceLaw, Measure.pi_pi]
  simp [PMF.toMeasure_apply_singleton, erasureCoin, PMF.bernoulli_apply]

theorem all_erased_probability_real {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (T : ℕ) :
    (erasureSequenceLaw u hu1 T {b | ∀ i, b i = true}).toReal = u ^ T := by
  rw [all_erased_probability, ENNReal.toReal_pow, ENNReal.toReal_ofReal hu0]

theorem erased_replies_zero {u : ℝ} {T : ℕ} (g : Fin T → ℝ)
    (b : Fin T → Bool) (hb : ∀ i, b i = true) :
    (fun i ↦ erasureReply u (g i) (b i)) = fun _ ↦ 0 := by
  funext i
  simp [erasureReply, hb i]

/-- Any random binary answer assigns mass at least one half to one answer. -/
theorem binary_answer_half_mass (q : PMF Bool) :
    ∃ b : Bool, (1 / 2 : ℝ) ≤ (q b).toReal := by
  have hsum : q false + q true = 1 := by
    simpa only [tsum_fintype, Fintype.sum_bool, add_comm] using q.tsum_coe
  have hsumR := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (q.apply_ne_top false) (q.apply_ne_top true),
    ENNReal.toReal_one] at hsumR
  by_cases ht : (1 / 2 : ℝ) ≤ (q true).toReal
  · exact ⟨true, ht⟩
  · exact ⟨false, by linarith⟩

/--
An arbitrary seed and a hypothesis-independent decoder cannot correctly test
both hidden binary hypotheses with probability greater than one half. Apply
`decode` to the algorithm's output on the identical erased transcript.
This is the testing component; adaptive transcript construction is separate.
-/
theorem identical_transcript_testing {S : Type*} [Fintype S]
    (seed : PMF S) (decode : S → Bool) :
    ∃ hypothesis : Bool,
      (1 / 2 : ℝ) ≤ ((seed.map decode) (!hypothesis)).toReal := by
  obtain ⟨b, hb⟩ := binary_answer_half_mass (seed.map decode)
  exact ⟨!b, by simpa using hb⟩

/-- Independent erasures and a common random answer force one testing error. -/
theorem erasure_testing_probability {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (T : ℕ) (q : PMF Bool) :
    ∃ hypothesis : Bool,
      u ^ T / 2 ≤
        (((erasureSequenceLaw u hu1 T).prod q.toMeasure)
          ({b | ∀ i, b i = true} ×ˢ {!hypothesis})).toReal := by
  obtain ⟨b, hb⟩ := binary_answer_half_mass q
  refine ⟨!b, ?_⟩
  simp only [Bool.not_not]
  rw [Measure.prod_prod, all_erased_probability,
    PMF.toMeasure_apply_singleton q b (MeasurableSet.singleton b),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hu0]
  have h := mul_le_mul_of_nonneg_left hb (pow_nonneg hu0 T)
  linarith

end HeavyTail
