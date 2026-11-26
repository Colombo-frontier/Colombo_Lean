import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Parity-compatible grid bias

This file makes the constructive arithmetic choice in Lemma `lem:grid-bias` explicit.
-/

namespace NCConcave16991.DenseWeakHiding

/-- Round `sqrt n` upward, adding one only when needed to match the parity of `n`. -/
noncomputable def parityRoundedSqrt (n : ℕ) : ℕ :=
  let c := Nat.ceil (Real.sqrt n)
  if c % 2 = n % 2 then c else c + 1

theorem parityRoundedSqrt_mod_two (n : ℕ) : parityRoundedSqrt n % 2 = n % 2 := by
  simp only [parityRoundedSqrt]
  split_ifs with h
  · exact h
  · omega

/-- The parity correction loses less than two above the real square root. -/
theorem parityRoundedSqrt_bounds (n : ℕ) :
    Real.sqrt n ≤ (parityRoundedSqrt n : ℝ) ∧
      (parityRoundedSqrt n : ℝ) ≤ Real.sqrt n + 2 := by
  let c := Nat.ceil (Real.sqrt n)
  have hcLower : Real.sqrt n ≤ (c : ℝ) := Nat.le_ceil _
  have hcUpper : (c : ℝ) < Real.sqrt n + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg n)
  dsimp [parityRoundedSqrt, c]
  split_ifs
  · exact ⟨hcLower, by linarith⟩
  · constructor
    · exact hcLower.trans (by norm_cast; omega)
    · push_cast
      linarith

/-- An explicit sufficient threshold for the manuscript's bound `m ≤ n/8`. -/
theorem parityRoundedSqrt_le_eighth {n : ℕ} (hn : 256 ≤ n) :
    (parityRoundedSqrt n : ℝ) ≤ (n : ℝ) / 8 := by
  have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt n ≤ (n : ℝ) / 16 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hnR)]
  have hm := (parityRoundedSqrt_bounds n).2
  linarith

/-- Explicit real-valued form of the admissible bias interval. -/
theorem parityRoundedSqrt_ratio_bounds {n : ℕ} (hn : 256 ≤ n) :
    let m := parityRoundedSqrt n
    let ρ : ℝ := (m : ℝ) / n
    1 / Real.sqrt n ≤ ρ ∧ ρ ≤ 2 / Real.sqrt n := by
  dsimp only
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) hn)
  have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsqrt_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hnpos.le
  have hmLower := (parityRoundedSqrt_bounds n).1
  have hmUpper := (parityRoundedSqrt_bounds n).2
  have hsqrt16 : (16 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hnR
    have he : Real.sqrt (256 : ℝ) = 16 :=
      (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 16)).2 (by norm_num)
    rwa [he] at h
  constructor
  · apply (div_le_div_iff₀ hsqrtpos hnpos).2
    nlinarith
  · apply (div_le_div_iff₀ hnpos hsqrtpos).2
    nlinarith

/-- Squaring the reciprocal bias gives the interval used to optimize the row cost. -/
theorem parityRoundedSqrt_invSq_bounds {n : ℕ} (hn : 256 ≤ n) :
    let m := parityRoundedSqrt n
    let ρ : ℝ := (m : ℝ) / n
    (n : ℝ) / 4 ≤ (ρ⁻¹) ^ 2 ∧ (ρ⁻¹) ^ 2 ≤ n := by
  dsimp only
  let ρ : ℝ := (parityRoundedSqrt n : ℝ) / n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 256) hn)
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsqrt_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hnpos.le
  obtain ⟨hρlower, hρupper⟩ := parityRoundedSqrt_ratio_bounds hn
  have hρpos : 0 < ρ := lt_of_lt_of_le (div_pos zero_lt_one hsqrtpos) hρlower
  have hinvLower : Real.sqrt n / 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρpos).2
    have hmul := mul_le_mul_of_nonneg_left hρupper (by positivity : 0 ≤ Real.sqrt n / 2)
    calc
      Real.sqrt n / 2 * ρ ≤ Real.sqrt n / 2 * (2 / Real.sqrt n) := hmul
      _ = 1 := by field_simp
  have hinvUpper : ρ⁻¹ ≤ Real.sqrt n := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hρpos).2
    have hmul := mul_le_mul_of_nonneg_left hρlower hsqrtpos.le
    calc
      1 = Real.sqrt n * (1 / Real.sqrt n) := by field_simp
      _ ≤ Real.sqrt n * ρ := hmul
  have hsquareLower := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt n / 2) hinvLower 2
  have hsquareUpper := pow_le_pow_left₀ (inv_nonneg.mpr hρpos.le) hinvUpper 2
  constructor
  · calc
      (n : ℝ) / 4 = (Real.sqrt n / 2) ^ 2 := by rw [div_pow, hsqrt_sq]; norm_num
      _ ≤ ρ⁻¹ ^ 2 := hsquareLower
  · calc
      ρ⁻¹ ^ 2 ≤ (Real.sqrt n) ^ 2 := hsquareUpper
      _ = n := hsqrt_sq

end NCConcave16991.DenseWeakHiding

/- Adapted from the local 0105_formalization/Manuscript0105/GridBias.lean. These analytic lemmas are reused for the cited dense weak hiding dependency; they do not assert its oracle lower bound. -/
