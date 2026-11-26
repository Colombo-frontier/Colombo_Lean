import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Algebraic certificates for the lower construction in 0113.tex

This module proves the compensated-lift identities and exact real-number rate
scaling. It does not assert the analytic cutoff estimates, random-frame coupling,
or minimax lower bound. The function `coreLower` is the *untruncated* linear core
of (lb:eq:g-lower), not the globally clipped lower objective in the paper.
-/

namespace Bilevel.LowerAlgebra

open scoped BigOperators
noncomputable section

/-- The scalar, untruncated compensated lower objective, with residual value `r`. -/
def coreLower (μ L x u s r : ℝ) : ℝ :=
  μ / 2 * u ^ 2 - L * x * u + μ / 2 * s ^ 2 +
    μ / (2 * L ^ 2) * r ^ 2 - μ / L * r * s

/-- Completion of both squares makes the compensation mechanism explicit. -/
theorem coreLower_complete_square (μ L x u s r : ℝ)
    (hμ : μ ≠ 0) (hL : L ≠ 0) :
    coreLower μ L x u s r =
      μ / 2 * (u - L / μ * x) ^ 2 + μ / 2 * (s - r / L) ^ 2 -
        L ^ 2 / (2 * μ) * x ^ 2 := by
  unfold coreLower
  field_simp
  ring

/-- For any residual function the untruncated core has the advertised response. -/
theorem coreLower_global_minimum (μ L x : ℝ) (r : ℝ → ℝ)
    (hμ : 0 < μ) (hL : L ≠ 0) (u s : ℝ) :
    coreLower μ L x (L / μ * x) (r (L / μ * x) / L) (r (L / μ * x)) ≤
      coreLower μ L x u s (r u) := by
  rw [coreLower_complete_square μ L x _ _ _ (ne_of_gt hμ) hL,
    coreLower_complete_square μ L x _ _ _ (ne_of_gt hμ) hL]
  have hu := sq_nonneg (u - L / μ * x)
  have hs := sq_nonneg (s - r u / L)
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
  nlinarith

/-- The response of the untruncated core is unique, without assuming convexity. -/
theorem coreLower_equality_iff (μ L x : ℝ) (r : ℝ → ℝ)
    (hμ : 0 < μ) (hL : L ≠ 0) (u s : ℝ) :
    coreLower μ L x u s (r u) =
        coreLower μ L x (L / μ * x) (r (L / μ * x) / L) (r (L / μ * x)) ↔
      u = L / μ * x ∧ s = r u / L := by
  rw [coreLower_complete_square μ L x _ _ _ (ne_of_gt hμ) hL,
    coreLower_complete_square μ L x _ _ _ (ne_of_gt hμ) hL]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
  constructor
  · intro heq
    have hu := sq_nonneg (u - L / μ * x)
    have hs := sq_nonneg (s - r u / L)
    have hu0 : (u - L / μ * x) ^ 2 = 0 := by nlinarith
    have hs0 : (s - r u / L) ^ 2 = 0 := by nlinarith
    constructor <;> nlinarith [hu0, hs0]
  · rintro ⟨hu, hs⟩
    rw [hs, hu]
    ring

/-- Cancellation in the `u` stationarity equation of the clipped lift.
The hypotheses state only the finite decomposition and the cutoff values at
the candidate response; global regularity is a separate analytic obligation. -/
theorem clipped_u_stationarity {ι : Type*} (S : Finset ι)
    (μ L x r dr : ℝ) (de q : ι → ℝ) (hμ : μ ≠ 0) (hL : L ≠ 0)
    (hde : ∑ j ∈ S, de j = dr)
    (hq : ∀ j ∈ S, q j = r / L) :
    μ * (L / μ * x) - L * x + μ / L ^ 2 * r * dr -
      μ / L * (∑ j ∈ S, de j * q j) = 0 := by
  have hsum : (∑ j ∈ S, de j * q j) = dr * (r / L) := by
    calc
      (∑ j ∈ S, de j * q j) = ∑ j ∈ S, de j * (r / L) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hq j hj]
      _ = (∑ j ∈ S, de j) * (r / L) := by rw [Finset.sum_mul]
      _ = dr * (r / L) := by rw [hde]
  rw [hsum]
  field_simp
  ring

/-- Cancellation in the `s` stationarity equation of the clipped lift. -/
theorem clipped_s_stationarity {ι : Type*} (S : Finset ι)
    (μ L r : ℝ) (e dq : ι → ℝ)
    (he : ∑ j ∈ S, e j = r)
    (hq : ∀ j ∈ S, dq j = 1) :
    μ * (r / L) - μ / L * (∑ j ∈ S, e j * dq j) = 0 := by
  have hsum : (∑ j ∈ S, e j * dq j) = r := by
    calc
      (∑ j ∈ S, e j * dq j) = ∑ j ∈ S, e j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hq j hj, mul_one]
      _ = r := he
  rw [hsum]
  ring

/-- Exact substitution into the upper objective, equation (lb:eq:exact-F). -/
theorem hyperobjective_substitution (L κ x : ℝ) (A R H : ℝ → ℝ)
    (hL : L ≠ 0) (hdecomp : ∀ u, A u + R u = H u) :
    A (κ * x) + L * (R (κ * x) / L) = H (κ * x) := by
  have hc : L * (R (κ * x) / L) = R (κ * x) := by field_simp
  rw [hc, hdecomp]

/-- The two exponent identities used for interior multiscale blocks. -/
theorem multiscale_exponents (t : ℝ) :
    2 * (1 - t / 4) - (1 - t / 2) = 1 ∧
      2 * (1 - t / 2) - (1 - t) = 1 := by
  constructor <;> ring

/-- Exact squared informative-amplitude scaling before numerical constants. -/
theorem informative_amplitude_scaling (c ε κ L θ : ℝ)
    (hκ : κ ≠ 0) (hL : L ≠ 0) (hθ : θ ≠ 0) :
    ((L / κ) * (c * ε / (κ * L)) ^ 2 / θ) ^ 2 =
      c ^ 4 * ε ^ 4 / (θ ^ 2 * κ ^ 6 * L ^ 2) := by
  field_simp
  ring

/-- Real-valued chain-length scale; integer rounding is not hidden here. -/
theorem chain_length_scaling (c ε κ L Δ : ℝ)
    (hc : c ≠ 0) (hε : ε ≠ 0) (hL : L ≠ 0) :
    Δ / (L * (c * ε / (κ * L)) ^ 2) = κ ^ 2 * L * Δ / (c ^ 2 * ε ^ 2) := by
  field_simp
  ring

/-- Combining the chain length with inverse squared informative amplitude
gives the sixth-power noise term of (lb:eq:lower-final). This is an algebraic
identity, not an oracle-complexity lower-bound theorem. -/
theorem stochastic_rate_scaling (c ε κ L θ Δ σ : ℝ)
    (hc : c ≠ 0) (hε : ε ≠ 0) (hL : L ≠ 0) :
    Δ / (L * (c * ε / (κ * L)) ^ 2) *
        (σ ^ 2 / ((L / κ) * (c * ε / (κ * L)) ^ 2 / θ) ^ 2) =
      θ ^ 2 * κ ^ 8 * σ ^ 2 * L ^ 3 * Δ / (c ^ 6 * ε ^ 6) := by
  field_simp
  ring

/- The fixed-horizon cost `T/p` in the multiscale proof is the sum of the
deterministic chain-length term and the stochastic sixth-power term.  This is
pure algebra: the probabilistic statement that an algorithm needs that many
calls is supplied separately by the transcript/testing lemmas. -/
theorem multiscale_horizon_over_activation (c ε κ L θ Δ σ : ℝ)
    (hc : c ≠ 0) (hε : ε ≠ 0) (hκ : κ ≠ 0) (hL : L ≠ 0)
    (hθ : θ ≠ 0) :
    let β := c * ε / (κ * L)
    let B := (L / κ) * β ^ 2 / θ
    let p := B ^ 2 / (σ ^ 2 + B ^ 2)
    let T := Δ / (L * β ^ 2)
    T / p =
      κ ^ 2 * L * Δ / (c ^ 2 * ε ^ 2) +
        θ ^ 2 * κ ^ 8 * σ ^ 2 * L ^ 3 * Δ /
          (c ^ 6 * ε ^ 6) := by
  dsimp
  have hβ : c * ε / (κ * L) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hc hε) (mul_ne_zero hκ hL)
  have hB : (L / κ) * (c * ε / (κ * L)) ^ 2 / θ ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (div_ne_zero hL hκ) (pow_ne_zero 2 hβ)) hθ
  have hBsq : 0 < ((L / κ) * (c * ε / (κ * L)) ^ 2 / θ) ^ 2 :=
    sq_pos_of_ne_zero hB
  have hden : σ ^ 2 + ((L / κ) * (c * ε / (κ * L)) ^ 2 / θ) ^ 2 ≠ 0 := by
    positivity
  field_simp [hβ, hB, hden, hc, hε, hκ, hL, hθ]
  ring

/- The floor in the manuscript's choice `T = floor(c_T Δ/(L β²))` costs at
most a factor two once the real-valued scale is at least two. -/
theorem natFloor_half_lower (A : ℝ) (hA : 2 ≤ A) :
    A / 2 ≤ (Nat.floor A : ℝ) := by
  have hnonneg : 0 ≤ A := by linarith
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one A
  norm_num at hlo hhi ⊢
  linarith

theorem rounded_horizon_threshold (A p : ℝ) (hA : 2 ≤ A) (hp : 0 < p) :
    A / (32 * p) ≤ (Nat.floor A : ℝ) / (16 * p) := by
  have hfloor := natFloor_half_lower A hA
  have hA0 : A ≠ 0 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hfloor
    (show 0 ≤ (16 * p)⁻¹ by positivity)
  have hleft : A / 2 * (16 * p)⁻¹ = A / (32 * p) := by
    field_simp [hp.ne', hA0]
    ring
  have hright : (Nat.floor A : ℝ) * (16 * p)⁻¹ =
      (Nat.floor A : ℝ) / (16 * p) := by
    field_simp [hp.ne']
  rw [hleft, hright] at hmul
  exact hmul

/- Combining `rounded_horizon_threshold` with the exact `T/p` identity gives
the integer fixed-horizon threshold used by the source proof.  The theorem is
still only an algebraic bridge; transcript coupling and the minimax argument
remain separate hypotheses in the surrounding modules. -/
theorem multiscale_rounded_horizon_threshold (cT c ε κ L θ Δ σ : ℝ)
    (hcT : cT > 0) (hc : c ≠ 0) (hε : ε ≠ 0) (hκ : κ ≠ 0) (hL : L ≠ 0)
    (hθ : θ ≠ 0)
    (hA : 2 ≤ cT * Δ / (L * (c * ε / (κ * L)) ^ 2)) :
    let β := c * ε / (κ * L)
    let B := (L / κ) * β ^ 2 / θ
    let p := B ^ 2 / (σ ^ 2 + B ^ 2)
    let T := Nat.floor (cT * Δ / (L * β ^ 2))
    (cT / 32) *
        (κ ^ 2 * L * Δ / (c ^ 2 * ε ^ 2) +
          θ ^ 2 * κ ^ 8 * σ ^ 2 * L ^ 3 * Δ / (c ^ 6 * ε ^ 6)) ≤
      (T : ℝ) / (16 * p) := by
  let β : ℝ := c * ε / (κ * L)
  let B : ℝ := (L / κ) * β ^ 2 / θ
  let p : ℝ := B ^ 2 / (σ ^ 2 + B ^ 2)
  let A : ℝ := cT * Δ / (L * β ^ 2)
  let T : ℕ := Nat.floor A
  have hβ : β ≠ 0 := by
    dsimp [β]
    exact div_ne_zero (mul_ne_zero hc hε) (mul_ne_zero hκ hL)
  have hB : B ≠ 0 := by
    dsimp [B]
    exact div_ne_zero (mul_ne_zero (div_ne_zero hL hκ) (pow_ne_zero 2 hβ)) hθ
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hp : 0 < p := by
    dsimp [p]
    exact div_pos hBsq (by positivity)
  have hA' : 2 ≤ A := by simpa [A, β] using hA
  have hΔ : Δ ≠ 0 := by
    intro hz
    have hzA : A = 0 := by
      dsimp [A]
      simp [hz]
    linarith
  have hcd : cT * Δ ≠ 0 := mul_ne_zero (ne_of_gt hcT) hΔ
  have hrough := rounded_horizon_threshold A p hA' hp
  have hid := multiscale_horizon_over_activation c ε κ L θ Δ σ hc hε hκ hL hθ
  have hrewrite : A / (32 * p) = (cT / 32) *
      (κ ^ 2 * L * Δ / (c ^ 2 * ε ^ 2) +
        θ ^ 2 * κ ^ 8 * σ ^ 2 * L ^ 3 * Δ / (c ^ 6 * ε ^ 6)) := by
    have hAeq : A / (32 * p) = (cT / 32) *
        (Δ / (L * β ^ 2) / p) := by
      dsimp [A]
      field_simp [hβ, hp.ne', hL, hc, hε, hκ, hcd]
      ring
    rw [hAeq]
    have hid' : Δ / (L * β ^ 2) / p =
        κ ^ 2 * L * Δ / (c ^ 2 * ε ^ 2) +
          θ ^ 2 * κ ^ 8 * σ ^ 2 * L ^ 3 * Δ / (c ^ 6 * ε ^ 6) := by
      simpa [β, B, p] using hid
    rw [hid']
  have hfinal : (cT / 32) *
      (κ ^ 2 * L * Δ / (c ^ 2 * ε ^ 2) +
        θ ^ 2 * κ ^ 8 * σ ^ 2 * L ^ 3 * Δ / (c ^ 6 * ε ^ 6)) ≤
      (Nat.floor A : ℝ) / (16 * p) := by
    rw [← hrewrite]
    exact hrough
  simpa [T, A, p, B, β] using hfinal

end
end Bilevel.LowerAlgebra
