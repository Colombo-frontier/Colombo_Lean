import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Arithmetic for the chi-refinement manuscript (2026-11-23)

These are identities and inequalities between the displayed rate expressions.
They do not assert existence of an SFO algorithm or of hard instances. In
particular, `normalizedExpansion_le_six_rates` only simplifies the expression
in `eq:main-upper-normalized`; it does not prove that expression is an upper
bound on query complexity.

Fractional powers are represented by natural powers times `Real.sqrt`.
`deterministic_eq_rpow` identifies this convention with the source exponent.
-/

noncomputable section
namespace Bilevel.ChiRefinementRates

def deterministic (L θ κ Δ ε : ℝ) : ℝ :=
  L * (1 + θ) * κ ^ 2 * Real.sqrt κ * Δ / ε ^ 2

def upperNoise (L κ σf Δ ε : ℝ) : ℝ :=
  L * κ ^ 4 * σf ^ 2 * Δ / ε ^ 4

def lowerNoise (L θ κ σg Δ ε : ℝ) : ℝ :=
  L ^ 3 * θ ^ 2 * (1 + θ) * κ ^ 8 * σg ^ 2 * Δ / ε ^ 6

def normalizedExpansion (L θ κ σf σg Δ ε : ℝ) : ℝ :=
  (1 + (1 + θ) * (L * κ ^ 2 * Δ / ε ^ 2)) *
    (Real.sqrt κ + κ ^ 2 * σg ^ 2 / ε ^ 2 +
      L ^ 2 * θ ^ 2 * κ ^ 6 * σg ^ 2 / ε ^ 4) +
  (1 + L * κ ^ 2 * Δ / ε ^ 2) *
    (1 + κ ^ 2 * σf ^ 2 / ε ^ 2 + κ ^ 4 * σg ^ 2 / ε ^ 2)

theorem deterministic_eq_rpow {κ : ℝ} (hκ : 0 ≤ κ) (L θ Δ ε : ℝ) :
    deterministic L θ κ Δ ε = L * (1 + θ) * κ ^ (5 / 2 : ℝ) * Δ / ε ^ 2 := by
  rcases hκ.eq_or_lt with rfl | hκ
  · norm_num [deterministic]
  have hp : κ ^ (5 / 2 : ℝ) = κ ^ (2 : ℕ) * Real.sqrt κ := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hκ,
      Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [hp]
  unfold deterministic
  ring

theorem deterministic_nonneg {L θ κ Δ ε : ℝ}
    (hL : 0 ≤ L) (hθ : 0 ≤ θ) (hΔ : 0 ≤ Δ) :
    0 ≤ deterministic L θ κ Δ ε := by
  unfold deterministic
  positivity

theorem upperNoise_nonneg {L κ σf Δ ε : ℝ}
    (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) : 0 ≤ upperNoise L κ σf Δ ε := by
  unfold upperNoise
  positivity

theorem lowerNoise_nonneg {L θ κ σg Δ ε : ℝ}
    (hL : 0 ≤ L) (hθ : 0 ≤ θ) (hΔ : 0 ≤ Δ) :
    0 ≤ lowerNoise L θ κ σg Δ ε := by
  unfold lowerNoise
  positivity

theorem zero_noise (L θ κ Δ ε : ℝ) :
    upperNoise L κ 0 Δ ε = 0 ∧ lowerNoise L θ κ 0 Δ ε = 0 := by
  simp [upperNoise, lowerNoise]

/-- Exact upper-noise/deterministic crossover, allowing zero noise. -/
theorem upperNoise_crossover {L θ κ σf Δ ε : ℝ}
    (hκ : 0 < κ) (hε : ε ≠ 0)
    (hσ : σf ^ 2 = (1 + θ) * ε ^ 2 / (κ * Real.sqrt κ)) :
    upperNoise L κ σf Δ ε = deterministic L θ κ Δ ε := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsq := Real.sq_sqrt hκ.le
  unfold upperNoise deterministic
  rw [hσ]
  field_simp
  ring_nf
  rw [hsq]
  ring

/-- Exact lower-noise/deterministic crossover, with kappa^(11/2).
The equality remains meaningful when one or both terms are zero. -/
theorem lowerNoise_crossover {L θ κ σg Δ ε : ℝ}
    (hL : L ≠ 0) (hθ : θ ≠ 0) (hκ : 0 < κ) (hε : ε ≠ 0)
    (hσ : σg ^ 2 = ε ^ 4 / (L ^ 2 * θ ^ 2 * κ ^ 5 * Real.sqrt κ)) :
    lowerNoise L θ κ σg Δ ε = deterministic L θ κ Δ ε := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsq := Real.sq_sqrt hκ.le
  unfold lowerNoise deterministic
  rw [hσ]
  field_simp
  ring_nf
  rw [hsq]
  ring

/-- Exact crossover between the two noise terms. -/
theorem noise_crossover {L θ κ σf σg Δ ε : ℝ}
    (hL : L ≠ 0) (hθ : θ ≠ 0) (hχ : 1 + θ ≠ 0) (hκ : κ ≠ 0)
    (hε : ε ≠ 0)
    (hσ : σg ^ 2 = ε ^ 2 * σf ^ 2 / (L ^ 2 * θ ^ 2 * (1 + θ) * κ ^ 4)) :
    lowerNoise L θ κ σg Δ ε = upperNoise L κ σf Δ ε := by
  unfold lowerNoise upperNoise
  rw [hσ]
  field_simp
  ring

/-- Three separately proved lower estimates imply a sum estimate. The
estimates are explicit premises, not hard-instance existence certificates. -/
theorem sum_lower_of_three {T D U G : ℝ} (hD : D ≤ T) (hU : U ≤ T)
    (hG : G ≤ T) : (D + U + G) / 3 ≤ T := by
  linarith

theorem max_le_sum {D U G : ℝ} (hD : 0 ≤ D) (hU : 0 ≤ U) (hG : 0 ≤ G) :
    max D (max U G) ≤ D + U + G := by
  simp only [max_le_iff]
  constructor
  · linarith
  constructor <;> linarith

private theorem abstract_absorption {χ X s a b c u : ℝ}
    (hχ : 1 ≤ χ) (hX : 1 ≤ X) (hs : 1 ≤ s)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hu0 : 0 ≤ u)
    (ha : a ≤ c) (hb : b ≤ χ * c) :
    (1 + χ * X) * (s + a + c) + (1 + X) * (1 + u + b) ≤
      6 * (χ * X * s + X * u + χ * X * c) := by
  have hχ0 : 0 ≤ χ := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hχX : 1 ≤ χ * X := by nlinarith
  have hχXs : X ≤ χ * X * s := by
    have h1 : X ≤ χ * X := by nlinarith
    have h2 : χ * X ≤ χ * X * s := by nlinarith
    exact h1.trans h2
  have h1 : (1 + χ * X) * (s + a + c) ≤ 2 * (χ * X) * (s + a + c) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (1 + X) * (1 + u + b) ≤ 2 * X * (1 + u + b) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left ha (mul_nonneg hχ0 hX0)
  have h4 := mul_le_mul_of_nonneg_left hb hX0
  have h5 : 0 ≤ X * u := mul_nonneg hX0 hu0
  have h6 : 0 ≤ χ * X * s := by positivity
  nlinarith

private theorem noise_absorption {L θ κ σ ε : ℝ}
    (hθ : 1 ≤ θ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hεL : ε ^ 2 ≤ L ^ 2) :
    κ ^ 2 * σ ^ 2 / ε ^ 2 ≤ L ^ 2 * θ ^ 2 * κ ^ 6 * σ ^ 2 / ε ^ 4 ∧
    κ ^ 4 * σ ^ 2 / ε ^ 2 ≤
      (1 + θ) * (L ^ 2 * θ ^ 2 * κ ^ 6 * σ ^ 2 / ε ^ 4) := by
  have ht : 1 ≤ θ ^ 2 := one_le_pow₀ hθ
  have hk2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hk4 : 1 ≤ κ ^ 4 := one_le_pow₀ hκ
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hε4 : 0 < ε ^ 4 := pow_pos hε _
  have hcoef : ε ^ 2 ≤ L ^ 2 * θ ^ 2 := by nlinarith [sq_nonneg L]
  have hc2 : κ ^ 2 * ε ^ 2 ≤ L ^ 2 * θ ^ 2 * κ ^ 6 := by
    calc
      _ ≤ κ ^ 2 * (L ^ 2 * θ ^ 2) := mul_le_mul_of_nonneg_left hcoef (sq_nonneg κ)
      _ ≤ κ ^ 2 * (L ^ 2 * θ ^ 2) * κ ^ 4 :=
        le_mul_of_one_le_right (by positivity) hk4
      _ = _ := by ring
  have hc4 : κ ^ 4 * ε ^ 2 ≤ (1 + θ) * (L ^ 2 * θ ^ 2 * κ ^ 6) := by
    calc
      _ ≤ κ ^ 4 * (L ^ 2 * θ ^ 2) := mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ ≤ κ ^ 4 * (L ^ 2 * θ ^ 2) * κ ^ 2 :=
        le_mul_of_one_le_right (by positivity) hk2
      _ ≤ (1 + θ) * (κ ^ 4 * (L ^ 2 * θ ^ 2) * κ ^ 2) := by
        have : 0 ≤ κ ^ 4 * (L ^ 2 * θ ^ 2) * κ ^ 2 := by positivity
        nlinarith
      _ = _ := by ring
  constructor
  · apply (div_le_div_iff₀ hε2 hε4).2
    nlinarith [mul_le_mul_of_nonneg_right hc2
      (by positivity : 0 ≤ σ ^ 2 * ε ^ 2)]
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hε2 hε4).2
    nlinarith [mul_le_mul_of_nonneg_right hc4
      (by positivity : 0 ≤ σ ^ 2 * ε ^ 2)]

/-- Floors and the fourth-power lower-noise terms in the normalized
expression are absorbed uniformly, including zero noise budgets. -/
theorem normalizedExpansion_le_six_rates {L θ κ σf σg Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hθ : 1 ≤ θ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hεL : ε ^ 2 ≤ L ^ 2) (hεΔ : ε ^ 2 ≤ L * Δ) :
    normalizedExpansion L θ κ σf σg Δ ε ≤
      6 * (deterministic L θ κ Δ ε + upperNoise L κ σf Δ ε +
        lowerNoise L θ κ σg Δ ε) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hk2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hX : 1 ≤ L * κ ^ 2 * Δ / ε ^ 2 := by
    apply (one_le_div (sq_pos_of_pos hε)).2
    have := mul_le_mul_of_nonneg_left hk2 (le_of_lt (mul_pos hL hΔ))
    nlinarith
  obtain ⟨ha, hb⟩ := noise_absorption (σ := σg) hθ hκ hε hεL
  have habs := abstract_absorption (χ := 1 + θ)
    (X := L * κ ^ 2 * Δ / ε ^ 2) (s := Real.sqrt κ)
    (a := κ ^ 2 * σg ^ 2 / ε ^ 2) (b := κ ^ 4 * σg ^ 2 / ε ^ 2)
    (c := L ^ 2 * θ ^ 2 * κ ^ 6 * σg ^ 2 / ε ^ 4)
    (u := κ ^ 2 * σf ^ 2 / ε ^ 2)
    (by linarith) hX (Real.one_le_sqrt.mpr hκ)
    (by positivity) (by positivity) (by positivity) (by positivity) ha hb
  unfold normalizedExpansion deterministic upperNoise lowerNoise
  convert habs using 1
  ring

/-- The source's uniform accuracy window (with numerical constant at most
one) is enough for the preceding algebraic absorption. No upper bound on
theta is needed for this upper-rate simplification. -/
theorem normalizedExpansion_le_six_rates_of_accuracy {L θ κ σf σg Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hθ : 1 ≤ θ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (haccuracy : ε ≤ min L (Real.sqrt (L * Δ))) :
    normalizedExpansion L θ κ σf σg Δ ε ≤
      6 * (deterministic L θ κ Δ ε + upperNoise L κ σf Δ ε +
        lowerNoise L θ κ σg Δ ε) := by
  have heL : ε ≤ L := haccuracy.trans (min_le_left _ _)
  have heΔ : ε ≤ Real.sqrt (L * Δ) := haccuracy.trans (min_le_right _ _)
  have hsq := Real.sq_sqrt (le_of_lt (mul_pos hL hΔ))
  have hroot := Real.sqrt_nonneg (L * Δ)
  apply normalizedExpansion_le_six_rates hL hΔ hθ hκ hε
  · nlinarith
  · nlinarith

end Bilevel.ChiRefinementRates
