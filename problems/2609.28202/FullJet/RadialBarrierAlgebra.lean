import Mathlib.Tactic

namespace FullJet

/-- Squared norm of one radial gradient block, in alignment/radius coordinates. -/
noncomputable def radialGradientSq (q ζ c : ℝ) : ℝ :=
  (33 / 16 : ℝ) ^ 2 * (ζ⁻¹ - 1) - 2 * (33 / 16) * c * q * ζ +
    c ^ 2 * ζ * (1 - q ^ 2 - q ^ 2 * ζ)

theorem radial_coefficient_nonneg (q ζ : ℝ) (hζ : 0 < ζ) (hqζ : ζ + q ^ 2 ≤ 1) :
    0 ≤ 1 - q ^ 2 - q ^ 2 * ζ := by
  have h := mul_le_mul_of_nonneg_right hqζ hζ.le
  nlinarith [sq_nonneg ζ]

theorem radial_coefficient_gap (q ζ : ℝ) (hζ : 0 < ζ) (hqζ : ζ + q ^ 2 ≤ 1)
    (hq : q ≤ 9 / 32) : 0 ≤ 1 - q ^ 2 - q ^ 2 * ζ - (33 / 16) * q := by
  by_cases hq0 : 0 ≤ q
  · have hq2 : q ^ 2 ≤ (9 / 32 : ℝ) ^ 2 := by nlinarith
    have hz1 : ζ ≤ 1 := by nlinarith [sq_nonneg q]
    have hprod := mul_le_mul_of_nonneg_left hz1 (sq_nonneg q)
    nlinarith
  · have h := radial_coefficient_nonneg q ζ hζ hqζ
    linarith

/-- Increasing the active coefficient above one cannot reduce this norm. -/
theorem radialGradientSq_ge_one_coefficient (q ζ c : ℝ) (hζ : 0 < ζ)
    (hqζ : ζ + q ^ 2 ≤ 1) (hq : q ≤ 9 / 32) (hc : 1 ≤ c) :
    radialGradientSq q ζ 1 ≤ radialGradientSq q ζ c := by
  have hD := radial_coefficient_nonneg q ζ hζ hqζ
  have hgap := radial_coefficient_gap q ζ hζ hqζ hq
  have hb : 0 ≤ (c + 1) * (1 - q ^ 2 - q ^ 2 * ζ) - 2 * (33 / 16) * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hD]
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) hζ.le) hb
  unfold radialGradientSq
  nlinarith

theorem radialGradientSq_nonneg_alignment (q ζ : ℝ) (hζ : 0 < ζ)
    (hqζ : ζ + q ^ 2 ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 9 / 32) :
    (1 / 16 : ℝ) ≤ radialGradientSq q ζ 1 := by
  let u := 1 - q ^ 2
  have hzu : ζ ≤ u := by dsimp [u]; linarith
  have hu : 0 < u := hζ.trans_le hzu
  have hu1 : u ≤ 1 := by dsimp [u]; nlinarith [sq_nonneg q]
  have hz1 : ζ ≤ 1 := hzu.trans hu1
  have hproduct : ζ * u ≤ 1 := (mul_le_mul hz1 hu1 hu.le zero_le_one).trans_eq (one_mul 1)
  have hdiv : 1 ≤ (33 / 16 : ℝ) ^ 2 / (ζ * u) :=
    (le_div_iff₀ (mul_pos hζ hu)).mpr (by nlinarith)
  have hb : 0 ≤ (33 / 16 : ℝ) ^ 2 / (ζ * u) - u + 2 * (33 / 16) * q +
      q ^ 2 * (ζ + u) := by
    have hlast : 0 ≤ q ^ 2 * (ζ + u) := mul_nonneg (sq_nonneg q) (by linarith)
    exact add_nonneg (add_nonneg (sub_nonneg.mpr (hu1.trans hdiv))
      (mul_nonneg (by norm_num) hq0)) hlast
  have hd := mul_nonneg (sub_nonneg.mpr hzu) hb
  have hid : radialGradientSq q ζ 1 - radialGradientSq q u 1 =
      (u - ζ) * ((33 / 16 : ℝ) ^ 2 / (ζ * u) - u + 2 * (33 / 16) * q + q ^ 2 * (ζ + u)) := by
    unfold radialGradientSq
    dsimp [u]
    field_simp
    <;> ring
  have hmono : radialGradientSq q u 1 ≤ radialGradientSq q ζ 1 := by rw [← hid] at hd; linarith
  have hq2 : q ^ 2 ≤ (9 / 32 : ℝ) ^ 2 := by nlinarith
  have hnum : (1 / 4 : ℝ) ≤ u ^ 2 - (33 / 16) * q := by
    dsimp [u]
    nlinarith [sq_nonneg (q ^ 2)]
  have hsq : (1 / 16 : ℝ) ≤ (u ^ 2 - (33 / 16) * q) ^ 2 := by nlinarith
  have heq : radialGradientSq q u 1 = (u ^ 2 - (33 / 16) * q) ^ 2 / u := by
    unfold radialGradientSq
    dsimp [u]
    field_simp
    <;> ring
  rw [heq] at hmono
  have hlow : (1 / 16 : ℝ) ≤ (u ^ 2 - (33 / 16) * q) ^ 2 / u :=
    (le_div_iff₀ hu).mpr (by nlinarith)
  exact hlow.trans hmono

theorem radialGradientSq_nonpos_alignment (q ζ : ℝ) (hζ : 0 < ζ)
    (hqζ : ζ + q ^ 2 ≤ 1) (hq : q ≤ 0) :
    1 ≤ radialGradientSq q ζ 1 := by
  have hz1 : ζ ≤ 1 := by nlinarith [sq_nonneg q]
  have hinv : 1 - ζ ≤ ζ⁻¹ - 1 := by
    have h : (1 - ζ) * ζ ≤ 1 - ζ := by nlinarith [sq_nonneg (1 - ζ)]
    have h' : 2 - ζ ≤ ζ⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hζ]
      nlinarith [sq_nonneg (1 - ζ)]
    linarith
  have hD : ζ ^ 2 ≤ 1 - q ^ 2 - q ^ 2 * ζ := by
    have h := mul_le_mul_of_nonneg_right hqζ hζ.le
    nlinarith
  have hD' := mul_le_mul_of_nonneg_left hD hζ.le
  have hcubic : 1 - 3 * (1 - ζ) ≤ ζ ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (1 - ζ)) (show 0 ≤ ζ + 2 by linarith)]
  have hcross : 0 ≤ -(2 * (33 / 16 : ℝ) * q * ζ) := by
    have := mul_nonpos_of_nonpos_of_nonneg hq hζ.le
    linarith
  unfold radialGradientSq
  nlinarith

/-- A convenient rational lower bound; the cited construction proves a sharper constant. -/
theorem radialGradientSq_lower_bound (q ζ c : ℝ) (hζ : 0 < ζ)
    (hqζ : ζ + q ^ 2 ≤ 1) (hq : q ≤ 9 / 32) (hc : 1 ≤ c) :
    (1 / 16 : ℝ) ≤ radialGradientSq q ζ c := by
  apply le_trans _ (radialGradientSq_ge_one_coefficient q ζ c hζ hqζ hq hc)
  rcases le_total 0 q with h | h
  · exact radialGradientSq_nonneg_alignment q ζ hζ hqζ h hq
  · exact le_trans (by norm_num) (radialGradientSq_nonpos_alignment q ζ hζ hqζ h)

end FullJet
