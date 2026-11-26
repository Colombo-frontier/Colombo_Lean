import Bilevel.ConditionalConfidence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Data.Complex.ExponentialBounds

/-!
# A conditional exponential bound for bad events

The exponential moment is proved from conditional bad-event probabilities,
not independence. We use exponential parameter 1: `exp(1) < 3` gives a
one-step factor at most `9/8 ≤ exp(1/8)`. This yields the manuscript's
`exp(-q/8)` tail at bad-count threshold `q/4`.
-/

noncomputable section
open MeasureTheory
namespace Bilevel.ConditionalConfidence

section Tail
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

def flag (s : Set Ω) : Ω → ℝ := s.indicator (fun _ => 1)

def count (B : ℕ → Set Ω) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => count B n ω + flag (B n) ω

def potential (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ := Real.exp (count B n ω)

theorem flag_bounds (s : Set Ω) (ω : Ω) : 0 ≤ flag s ω ∧ flag s ω ≤ 1 := by
  classical
  by_cases h : ω ∈ s <;> simp [flag, Set.indicator_apply, h]

theorem count_bounds (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    0 ≤ count B n ω ∧ count B n ω ≤ n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have hi := flag_bounds (B n) ω
    simp only [count, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith

theorem count_measurable_of_prefix (B : ℕ → Set Ω) (n : ℕ)
    (hB : ∀ i < n, MeasurableSet (B i)) : Measurable (count B n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih (fun i hi => hB i (Nat.lt_succ_of_lt hi))).add
      (measurable_const.indicator (hB n (Nat.lt_succ_self n)))

theorem potential_measurable_of_prefix (B : ℕ → Set Ω) (n : ℕ)
    (hB : ∀ i < n, MeasurableSet (B i)) : Measurable (potential B n) :=
  (count_measurable_of_prefix B n hB).exp

theorem potential_integrable [IsFiniteMeasure μ] (B : ℕ → Set Ω) (n : ℕ)
    (hB : ∀ i < n, MeasurableSet (B i)) : Integrable (potential B n) μ := by
  apply (integrable_const (Real.exp n)).mono'
    (potential_measurable_of_prefix B n hB).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, potential, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (count_bounds B n ω).2

theorem potential_succ (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    potential B (n + 1) ω = potential B n ω +
      (Real.exp 1 - 1) * (potential B n ω * flag (B n) ω) := by
  classical
  by_cases h : ω ∈ B n
  · simp [potential, count, flag, Set.indicator_apply, h, Real.exp_add]
    ring
  · simp [potential, count, flag, Set.indicator_apply, h]

theorem weighted_flag_bound [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) (s : Set Ω) (hs : MeasurableSet[m₀] s) (W : Ω → ℝ)
    (hWm : StronglyMeasurable[m] W) (hWi : Integrable W μ)
    (hprod : Integrable (fun ω => W ω * flag s ω) μ)
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hprob : ∀ᵐ ω ∂μ, (μ[flag s | m]) ω ≤ 1 / 16) :
    (∫ ω, W ω * flag s ω ∂μ) ≤ (1 / 16) * ∫ ω, W ω ∂μ := by
  letI : MeasurableSpace Ω := m₀
  have hI : Integrable (flag s) μ := (integrable_const (μ := μ) 1).indicator hs
  have hpull := condExp_mul_of_stronglyMeasurable_left hWm hprod hI
  have hcond : Integrable (fun ω => W ω * (μ[flag s | m]) ω) μ :=
    integrable_condExp.congr hpull
  calc
    _ = ∫ ω, (μ[(fun ω => W ω * flag s ω) | m]) ω ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ ω, W ω * (μ[flag s | m]) ω ∂μ := integral_congr_ae hpull
    _ ≤ ∫ ω, W ω * (1 / 16) ∂μ := by
      apply integral_mono_ae hcond (hWi.mul_const (1 / 16))
      filter_upwards [hprob] with ω hω
      exact mul_le_mul_of_nonneg_left hω (hW0 ω)
    _ = _ := by rw [integral_mul_const]; ring

/-- The full moment estimate uses conditional event probabilities with
respect to each run's past; the events need not be independent. -/
theorem potential_expectation_le [IsProbabilityMeasure μ]
    (B : ℕ → Set Ω) (past : ℕ → MeasurableSpace Ω)
    (hpast : ∀ n, past n ≤ m₀) (hmeas : ∀ n, MeasurableSet (B n))
    (hadapted : ∀ i n, i < n → MeasurableSet[past n] (B i))
    (hprob : ∀ n, ∀ᵐ ω ∂μ, (μ[flag (B n) | past n]) ω ≤ 1 / 16)
    (n : ℕ) : (∫ ω, potential B n ω ∂μ) ≤ Real.exp ((n : ℝ) / 8) := by
  induction n with
  | zero => simp [potential, count]
  | succ n ih =>
    have hWi := potential_integrable (μ := μ) B n (fun i _ => hmeas i)
    have hWm := potential_measurable_of_prefix B n (fun i _ => hmeas i)
    have hI : Integrable (flag (B n)) μ := (integrable_const 1).indicator (hmeas n)
    have hprod : Integrable (fun ω => potential B n ω * flag (B n) ω) μ := by
      apply hI.bdd_mul' (c := Real.exp n) hWm.aestronglyMeasurable
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, potential, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (count_bounds B n ω).2
    have hweight := weighted_flag_bound (hpast n) (B n) (hmeas n) (potential B n)
      (potential_measurable_of_prefix B n (fun i hi => hadapted i n hi)).stronglyMeasurable
      hWi hprod (fun ω => (Real.exp_pos _).le) (hprob n)
    have h0 : 0 ≤ ∫ ω, potential B n ω ∂μ := integral_nonneg fun _ => (Real.exp_pos _).le
    have he0 : 0 ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp 1; linarith
    have he3 : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    calc
      _ = (∫ ω, potential B n ω ∂μ) + (Real.exp 1 - 1) *
          (∫ ω, potential B n ω * flag (B n) ω ∂μ) := by
        simp_rw [potential_succ]
        rw [integral_add hWi (hprod.const_mul _), integral_const_mul]
      _ ≤ (9 / 8) * ∫ ω, potential B n ω ∂μ := by
        have hm := mul_le_mul_of_nonneg_left hweight he0
        have he := mul_le_mul_of_nonneg_right he3 h0
        nlinarith
      _ ≤ Real.exp (1 / 8) * ∫ ω, potential B n ω ∂μ := by
        apply mul_le_mul_of_nonneg_right _ h0
        have := Real.add_one_le_exp (1 / 8)
        linarith
      _ ≤ Real.exp (1 / 8) * Real.exp ((n : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- Conditional fresh-run bad indicators with probability at most 1/16
satisfy the exponential tail required by the confidence amplifier. -/
theorem bad_count_tail [IsProbabilityMeasure μ]
    (B : ℕ → Set Ω) (past : ℕ → MeasurableSpace Ω)
    (hpast : ∀ n, past n ≤ m₀) (hmeas : ∀ n, MeasurableSet (B n))
    (hadapted : ∀ i n, i < n → MeasurableSet[past n] (B i))
    (hprob : ∀ n, ∀ᵐ ω ∂μ, (μ[flag (B n) | past n]) ω ≤ 1 / 16)
    (n : ℕ) : μ.real {ω | (n : ℝ) / 4 ≤ count B n ω} ≤
      Real.exp (-(n : ℝ) / 8) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos (count B n ω)).le))
    (potential_integrable (μ := μ) B n (fun i _ => hmeas i)) (Real.exp ((n : ℝ) / 4))
  have hset : {ω | Real.exp ((n : ℝ) / 4) ≤ potential B n ω} =
      {ω | (n : ℝ) / 4 ≤ count B n ω} := by
    ext ω
    exact Real.exp_le_exp
  unfold potential at hset
  rw [hset] at hmarkov
  have hm := hmarkov.trans (potential_expectation_le B past hpast hmeas hadapted hprob n)
  have he : Real.exp (-(n : ℝ) / 8) * Real.exp ((n : ℝ) / 4) =
      Real.exp ((n : ℝ) / 8) := by rw [← Real.exp_add]; congr 1; ring
  apply (mul_le_mul_iff_of_pos_right (Real.exp_pos ((n : ℝ) / 4))).mp
  rw [he]
  simpa only [mul_comm] using hm

end Tail

section MSE
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Conditional Chebyshev at radius a/3 with the exact source constants. -/
theorem conditional_flag_of_mse {m : MeasurableSpace Ω} (_hm : m ≤ m₀)
    (loss : Ω → ℝ) (hmeas : Measurable[m₀] loss) (a : ℝ) (ha : 0 < a)
    (hsquare : Integrable (fun ω => loss ω ^ 2) μ)
    (hvariance : ∀ᵐ ω ∂μ, (μ[(fun ω => loss ω ^ 2) | m]) ω ≤ a ^ 2 / 144) :
    ∀ᵐ ω ∂μ, (μ[flag {ω | a / 3 < loss ω} | m]) ω ≤ 1 / 16 := by
  letI : MeasurableSpace Ω := m₀
  have hset : MeasurableSet {ω | a / 3 < loss ω} := measurableSet_lt measurable_const hmeas
  have hI : Integrable (flag {ω | a / 3 < loss ω}) μ :=
    (integrable_const 1).indicator hset
  have hcoef : 0 ≤ 9 / a ^ 2 := by positivity
  have hpoint : ∀ ω, flag {ω | a / 3 < loss ω} ω ≤ (9 / a ^ 2) * loss ω ^ 2 := by
    intro ω
    classical
    by_cases h : a / 3 < loss ω
    · simp only [flag, Set.indicator_apply, Set.mem_setOf_eq, h, if_true]
      have hb : a ^ 2 ≤ 9 * loss ω ^ 2 := by nlinarith
      calc
        (1 : ℝ) ≤ 9 * loss ω ^ 2 / a ^ 2 := (one_le_div (sq_pos_of_pos ha)).mpr hb
        _ = _ := by ring
    · simp only [flag, Set.indicator_apply, Set.mem_setOf_eq, h, if_false]
      positivity
  have hmono := condExp_mono (m := m) hI (hsquare.const_mul (9 / a ^ 2))
    (Filter.Eventually.of_forall hpoint)
  have hscale : μ[(fun ω => (9 / a ^ 2) * loss ω ^ 2) | m] =ᵐ[μ]
      fun ω => (9 / a ^ 2) * (μ[(fun ω => loss ω ^ 2) | m]) ω := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      condExp_smul (9 / a ^ 2) (fun ω => loss ω ^ 2) m
  filter_upwards [hmono, hscale, hvariance] with ω hmω hsω hvω
  calc
    _ ≤ (9 / a ^ 2) * (μ[(fun ω => loss ω ^ 2) | m]) ω := by rwa [hsω] at hmω
    _ ≤ (9 / a ^ 2) * (a ^ 2 / 144) := mul_le_mul_of_nonneg_left hvω hcoef
    _ = 1 / 16 := by field_simp; ring

/-- The count is exactly the number of bad candidates, not an abstract
dominating random variable. -/
theorem count_eq_sum (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    count B n ω = ∑ i ∈ Finset.range n, flag (B i) ω := by
  induction n with
  | zero => simp [count]
  | succ n ih => simp [count, Finset.sum_range_succ, ih]

variable {E : Type*} [PseudoMetricSpace E]

theorem count_eq_bad_card (Z : Ω → ℕ → E) (target : E) (a : ℝ) (q : ℕ) (ω : Ω) :
    count (fun n => {ω | a / 3 < dist (Z ω n) target}) q ω =
      ((bad (fun i : Fin q => Z ω i) target (a / 3)).card : ℝ) := by
  classical
  rw [count_eq_sum, ← Fin.sum_univ_eq_sum_range]
  simp [flag, Set.indicator_apply, bad]

/-- Complete pointwise-target confidence bound for the actual selector.
The assumptions are measurability/adaptation and conditional MSE of each
candidate; no unconditional independence or output error bound is assumed.
The ambient probability measure can be any fixed starting-history law. -/
theorem confidence_from_conditional_mse (Z : Ω → ℕ → E) (target : E)
    (past : ℕ → MeasurableSpace Ω) (hpast : ∀ n, past n ≤ m₀)
    (hmeas : ∀ n, Measurable (fun ω => dist (Z ω n) target))
    (hadapted : ∀ i n, i < n →
      Measurable[past n] (fun ω => dist (Z ω i) target))
    (a : ℝ) (ha : 0 < a)
    (hsquare : ∀ n, Integrable (fun ω => dist (Z ω n) target ^ 2) μ)
    (hmse : ∀ n, ∀ᵐ ω ∂μ,
      (μ[(fun ω => dist (Z ω n) target ^ 2) | past n]) ω ≤ a ^ 2 / 144)
    (q : ℕ) [NeZero q] :
    μ.real {ω | a < dist (select (fun i : Fin q => Z ω i)) target} ≤
      Real.exp (-(q : ℝ) / 8) := by
  let B : ℕ → Set Ω := fun n => {ω | a / 3 < dist (Z ω n) target}
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_lt measurable_const (hmeas n)
  have hBa : ∀ i n, i < n → MeasurableSet[past n] (B i) := fun i n hin =>
    measurableSet_lt measurable_const (hadapted i n hin)
  have hprob : ∀ n, ∀ᵐ ω ∂μ, (μ[flag (B n) | past n]) ω ≤ 1 / 16 := fun n =>
    conditional_flag_of_mse (hpast n) (fun ω => dist (Z ω n) target)
      (hmeas n) a ha (hsquare n) (hmse n)
  apply (measureReal_mono (s₂ := {ω | (q : ℝ) / 4 ≤ count B q ω}) ?_).trans
    (bad_count_tail B past hpast hB hBa hprob q)
  intro ω hω
  have hb := failure_subset_bad_count (fun ω i => Z ω i) target a hω
  have hcast : (q : ℝ) ≤ 4 * ((bad (fun i : Fin q => Z ω i) target (a / 3)).card : ℝ) :=
    by exact_mod_cast hb
  change (q : ℝ) / 4 ≤ count B q ω
  rw [show count B q ω = ((bad (fun i : Fin q => Z ω i) target (a / 3)).card : ℝ)
    from count_eq_bad_card Z target a q ω]
  linarith

end MSE
end Bilevel.ConditionalConfidence
