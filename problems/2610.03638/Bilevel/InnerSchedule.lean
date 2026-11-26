import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# A finite schedule for the sharp inner contraction

`initial` is the initial squared-distance bound; `radius` is the target
distance. The actual natural-number iteration count uses a ceiling, rather
than an asymptotic or existence-only statement.
-/

noncomputable section

namespace Bilevel.InnerSchedule

def stepsize (μ L σ radius : ℝ) : ℝ :=
  if σ = 0 then L⁻¹ else min L⁻¹ (μ * radius ^ 2 / (2 * σ ^ 2))

def logarithm (initial radius : ℝ) : ℝ :=
  Real.log (max 1 (2 * initial / radius ^ 2))

def iterations (μ L σ radius initial : ℝ) : ℕ :=
  ⌈(μ * stepsize μ L σ radius)⁻¹ * logarithm initial radius⌉₊

theorem stepsize_pos {μ L σ radius : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hr : 0 < radius) :
    0 < stepsize μ L σ radius := by
  unfold stepsize
  split_ifs with hσ
  · positivity
  · exact lt_min (inv_pos.mpr hL) (div_pos (mul_pos hμ (sq_pos_of_pos hr))
      (mul_pos (by norm_num) (sq_pos_of_ne_zero hσ)))

theorem stepsize_le_inverse {μ L σ radius : ℝ} : stepsize μ L σ radius ≤ L⁻¹ := by
  unfold stepsize
  split_ifs
  · rfl
  · exact min_le_left _ _

theorem noise_floor {μ L σ radius : ℝ} (hμ : 0 < μ) :
    stepsize μ L σ radius * σ ^ 2 / μ ≤ radius ^ 2 / 2 := by
  by_cases hσ : σ = 0
  · simp only [hσ, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
    positivity
  · have hs : stepsize μ L σ radius ≤ μ * radius ^ 2 / (2 * σ ^ 2) := by
      simpa only [stepsize, if_neg hσ] using min_le_right L⁻¹ (μ * radius ^ 2 / (2 * σ ^ 2))
    have hden : 0 < 2 * σ ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hσ)
    have hm := (le_div_iff₀ hden).mp hs
    apply (div_le_iff₀ hμ).mpr
    nlinarith

theorem contraction_range {μ L σ radius : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hr : 0 < radius) (hμL : μ ≤ L) :
    0 < μ * stepsize μ L σ radius ∧ μ * stepsize μ L σ radius ≤ 1 := by
  constructor
  · exact mul_pos hμ (stepsize_pos hμ hL hr)
  · calc
      μ * stepsize μ L σ radius ≤ μ * L⁻¹ :=
        mul_le_mul_of_nonneg_left stepsize_le_inverse hμ.le
      _ ≤ L * L⁻¹ := mul_le_mul_of_nonneg_right hμL (inv_nonneg.mpr hL.le)
      _ = 1 := mul_inv_cancel₀ hL.ne'

theorem logarithm_nonneg (initial radius : ℝ) : 0 ≤ logarithm initial radius :=
  Real.log_nonneg (le_max_left _ _)

/-- Exponential comparison gives a concrete iteration threshold. -/
theorem contraction_term {s radius initial : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hr : 0 < radius) (hinit : 0 ≤ initial) (n : ℕ)
    (hn : s⁻¹ * logarithm initial radius ≤ (n : ℝ)) :
    (1 - s) ^ n * initial ≤ radius ^ 2 / 2 := by
  let M := max 1 (2 * initial / radius ^ 2)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hexp : 1 - s ≤ Real.exp (-s) := by simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-s)
  have hp : (1 - s) ^ n ≤ Real.exp (-(s * n)) := by
    calc
      (1 - s) ^ n ≤ (Real.exp (-s)) ^ n := pow_le_pow_left₀ (sub_nonneg.mpr hs1) hexp n
      _ = Real.exp (-(s * n)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hn' : logarithm initial radius ≤ s * n := by
    have h := mul_le_mul_of_nonneg_left hn hs.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] using h
  have he : Real.exp (-(s * n)) ≤ M⁻¹ := by
    calc
      Real.exp (-(s * n)) ≤ Real.exp (-Real.log M) := Real.exp_le_exp.mpr (neg_le_neg hn')
      _ = M⁻¹ := by rw [Real.exp_neg, Real.exp_log hM]
  have hratio : 2 * initial / radius ^ 2 ≤ M := le_max_right _ _
  have hb : M⁻¹ * initial ≤ radius ^ 2 / 2 := by
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hM).mpr
    have h := (div_le_iff₀ (sq_pos_of_pos hr)).mp hratio
    nlinarith
  exact (mul_le_mul_of_nonneg_right (hp.trans he) hinit).trans hb

/-- The selected finite natural count reduces deterministic initialization error. -/
theorem iterations_contract {μ L σ radius initial : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hr : 0 < radius) (hμL : μ ≤ L) (hinit : 0 ≤ initial) :
    (1 - μ * stepsize μ L σ radius) ^ iterations μ L σ radius initial * initial ≤ radius ^ 2 / 2 := by
  obtain ⟨hs, hs1⟩ := contraction_range hμ hL hr hμL (σ := σ)
  apply contraction_term hs hs1 hr hinit
  exact Nat.le_ceil _

/-- Plugging the finite schedule into the sharp SGD recurrence meets the target. -/
theorem scheduled_error {μ L σ radius initial error : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hr : 0 < radius) (hμL : μ ≤ L) (hinit : 0 ≤ initial)
    (herror : error ≤
      (1 - μ * stepsize μ L σ radius) ^ iterations μ L σ radius initial * initial +
        stepsize μ L σ radius * σ ^ 2 / μ) : error ≤ radius ^ 2 := by
  have hc := iterations_contract hμ hL hr hμL hinit (σ := σ)
  have hn := noise_floor hμ (L := L) (radius := radius) (σ := σ)
  linarith

/-- The reciprocal contraction parameter has the required linear condition dependence. -/
theorem inverse_rate_le {μ L σ radius : ℝ} (hμ : 0 < μ) (hL : 0 < L) :
    (μ * stepsize μ L σ radius)⁻¹ ≤ L / μ + 2 * σ ^ 2 / (μ ^ 2 * radius ^ 2) := by
  have hleft : (μ * L⁻¹)⁻¹ = L / μ := by simp [mul_inv_rev, div_eq_mul_inv, mul_comm]
  have hright : (μ * (μ * radius ^ 2 / (2 * σ ^ 2)))⁻¹ =
      2 * σ ^ 2 / (μ ^ 2 * radius ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
    ring
  unfold stepsize
  split_ifs with hσ
  · simp [hσ, hleft]
  · rw [min_def]
    split_ifs
    · rw [hleft]
      exact le_add_of_nonneg_right (by positivity)
    · rw [hright]
      exact le_add_of_nonneg_left (by positivity)

/-- The logarithmic factor is bounded by a standard, always-positive logarithm. -/
theorem logarithm_le {initial radius : ℝ} (hinit : 0 ≤ initial) :
    logarithm initial radius ≤ 2 * Real.log (2 + initial / radius ^ 2) := by
  let u := initial / radius ^ 2
  have hu : 0 ≤ u := div_nonneg hinit (sq_nonneg _)
  have hm : max 1 (2 * u) ≤ (2 + u) ^ 2 := by
    apply max_le <;> nlinarith
  have hp : 0 < max 1 (2 * u) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h := Real.log_le_log hp hm
  rw [Real.log_pow] at h
  change Real.log (max 1 (2 * initial / radius ^ 2)) ≤ _
  convert h using 1
  dsimp [u]
  ring

/-- Explicit finite complexity bound, including the ceiling and zero-noise branch. -/
theorem iterations_le {μ L σ radius initial : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hr : 0 < radius) (hinit : 0 ≤ initial) :
    (iterations μ L σ radius initial : ℝ) ≤
      1 + 4 * (L / μ + σ ^ 2 / (μ ^ 2 * radius ^ 2)) * Real.log (2 + initial / radius ^ 2) := by
  have hη := stepsize_pos hμ hL hr (σ := σ)
  have hlog := logarithm_nonneg initial radius
  have harg : 0 ≤ (μ * stepsize μ L σ radius)⁻¹ * logarithm initial radius :=
    mul_nonneg (inv_nonneg.mpr (mul_pos hμ hη).le) hlog
  have hc := (Nat.ceil_lt_add_one harg).le
  have hmul := mul_le_mul (inverse_rate_le hμ hL (radius := radius) (σ := σ)) (logarithm_le (radius := radius) hinit)
    hlog (by positivity : 0 ≤ L / μ + 2 * σ ^ 2 / (μ ^ 2 * radius ^ 2))
  have hu : 0 ≤ initial / radius ^ 2 := by positivity
  have hlogpos : 0 ≤ Real.log (2 + initial / radius ^ 2) := Real.log_nonneg (by linarith)
  have hcoef : (L / μ + 2 * σ ^ 2 / (μ ^ 2 * radius ^ 2)) * 2 ≤
      4 * (L / μ + σ ^ 2 / (μ ^ 2 * radius ^ 2)) := by
    have h1 : 0 ≤ L / μ := by positivity
    have heq : (L / μ + 2 * σ ^ 2 / (μ ^ 2 * radius ^ 2)) * 2 =
        4 * (L / μ + σ ^ 2 / (μ ^ 2 * radius ^ 2)) - 2 * (L / μ) := by ring
    rw [heq]
    linarith
  have hlast := mul_le_mul_of_nonneg_right hcoef hlogpos
  dsimp [iterations]
  nlinarith

end Bilevel.InnerSchedule
