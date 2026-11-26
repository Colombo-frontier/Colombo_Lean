import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Explicit algebra behind the endpoint-only tolerance bound. These results
do not assert existence of an oracle algorithm or a minimax lower witness. -/
namespace SecondOrder

theorem mixed_term_le_endpoints {e g : ℝ} (he : 0 < e) (hg : 0 < g) :
    1 / (e ^ 2 * g) ≤ 1 / e ^ 3 + 1 / g ^ 3 := by
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  by_cases h : e ≤ g
  · have hden : e ^ 3 ≤ e ^ 2 * g := by nlinarith
    have := one_div_le_one_div_of_le (pow_pos he 3) hden
    exact this.trans (le_add_of_nonneg_right (by positivity))
  · have hge : g ≤ e := le_of_lt (lt_of_not_ge h)
    have hden : g ^ 3 ≤ e ^ 2 * g := by
      have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg.le hge 2) hg.le
      nlinarith
    have := one_div_le_one_div_of_le (pow_pos hg 3) hden
    exact this.trans (le_add_of_nonneg_left (by positivity))

theorem mixed_term_le_lipschitz_endpoints {e g : ℝ}
    (he : 0 < e) (hg : 0 < g) (hg1 : g ≤ 1) :
    1 / (e ^ 2 * g) ≤ 1 / e ^ 3 + 1 / g ^ 5 := by
  have hpow : g ^ 5 ≤ g ^ 3 := by
    have : g ^ 2 ≤ 1 := by nlinarith
    nlinarith [pow_nonneg hg.le 3, mul_nonneg (pow_nonneg hg.le 3) (sub_nonneg.mpr this)]
  exact (mixed_term_le_endpoints he hg).trans
    (add_le_add_left (one_div_le_one_div_of_le (pow_pos hg 5) hpow) _)

theorem mixed_term_le_holder_endpoints {e g ν : ℝ}
    (he : 0 < e) (hg : 0 < g) (hg1 : g ≤ 1) (hν : 0 < ν) :
    1 / (e ^ 2 * g) ≤ 1 / e ^ 3 + g ^ (-(3 + 2 / ν)) := by
  have hp : g ^ (3 + 2 / ν) ≤ g ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hg hg1 (by have := div_pos (by norm_num : (0 : ℝ) < 2) hν; linarith)
  have hinv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hg _) hp
  have heq : 1 / g ^ (3 : ℝ) = 1 / g ^ 3 := by norm_cast
  rw [heq] at hinv
  have hr : 1 / g ^ (3 + 2 / ν) = g ^ (-(3 + 2 / ν)) := by
    rw [Real.rpow_neg hg.le, one_div]
  rw [hr] at hinv
  exact (mixed_term_le_endpoints he hg).trans (add_le_add_left hinv _)

theorem endpoint_lower_sum {a b t : ℝ} (ha : a ≤ t) (hb : b ≤ t) :
    (a + b) / 2 ≤ t := by linarith

theorem clipped_balance_left {A B : ℝ} (h : A ≤ B) : A / 1 + B * 1 ≤ 2 * B := by
  linarith

theorem clipped_balance_right {A B Q : ℝ} (hQ : 0 < Q) (h : B * Q ^ 2 ≤ A) :
    A / Q + B * Q ≤ 2 * A / Q := by
  apply (le_div_iff₀ hQ).mpr
  field_simp
  nlinarith

theorem balance_exact {A B q : ℝ} (hq : 0 < q) (h : A = B * q ^ 2) :
    A / q + B * q = 2 * B * q := by
  rw [h]
  field_simp
  <;> ring

theorem balance_rounding {A B q Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq : 0 < q) (hlo : q ≤ Q) (hhi : Q ≤ 2 * q) :
    A / Q + B * Q ≤ 2 * (A / q + B * q) := by
  have hdiv : A / Q ≤ A / q := div_le_div_of_nonneg_left hA hq hlo
  have hmul := mul_le_mul_of_nonneg_left hhi hB
  have := div_nonneg hA hq.le
  nlinarith

theorem balanced_tolerance_cost {e A B : ℝ} (he : 0 < e) :
    A / ((1 / e) * e ^ 4) + B * (1 / e) / e ^ 2 = (A + B) / e ^ 3 := by
  field_simp
  <;> ring

theorem curvature_scale_lipschitz {L C g D : ℝ} (hL : L ≠ 0)
    (hC : C ≠ 0) (hg : g ≠ 0) (hD : D ≠ 0) :
    let β := L / (16 * C * g)
    let A := 8 * D * g / β ^ 2
    A * β ^ 2 / D = 8 * g ∧ A * β ^ 3 * C / D = L / 2 ∧
      A = 2048 * C ^ 2 * D * g ^ 3 / L ^ 2 := by
  dsimp
  constructor
  · field_simp
    <;> ring
  constructor <;> field_simp <;> ring

theorem success_probability_arithmetic {p f c w : ℝ}
    (hp : 1 - f - c - w ≤ p) (hf : f ≤ 1/96) (hc : c ≤ 1/24)
    (hw : w ≤ 1/24) : 3/4 < p := by linarith

end SecondOrder
