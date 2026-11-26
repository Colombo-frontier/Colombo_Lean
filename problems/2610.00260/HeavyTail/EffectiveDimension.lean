import HeavyTail.StatisticalSquares

/-! Exact effective-dimension rewritings from eq:effective, the confidence
coefficient gains, and the p=2 endpoint. These are scalar identities and
comparisons; model-level rate consequences use the proved main bounds. -/
noncomputable section
namespace HeavyTail

def momentDimension (L s : ℝ) : ℝ := L ^ 2 / s ^ 2

theorem momentDimension_pos {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    0 < momentDimension L s := by unfold momentDimension; positivity

theorem momentDimension_sqrt {L s : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s) :
    Real.sqrt (momentDimension L s) = L / s := by
  rw [momentDimension, Real.sqrt_div (sq_nonneg L), Real.sqrt_sq hL, Real.sqrt_sq hs]

theorem momentDimension_scale {L s : ℝ} (hL : 0 ≤ L) (hs : 0 < s) :
    s * Real.sqrt (momentDimension L s) = L := by
  rw [momentDimension_sqrt hL hs.le]
  field_simp

theorem momentDimension_inverse_scale {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    s = L / Real.sqrt (momentDimension L s) := by
  rw [momentDimension_sqrt hL.le hs.le]
  field_simp

theorem momentDimension_power {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (p : ℝ) :
    s * (momentDimension L s) ^ (1 - 1 / p) =
      L * (momentDimension L s) ^ (1 / 2 - 1 / p) := by
  have he := momentDimension_pos hL hs
  calc
    _ = s * ((momentDimension L s) ^ (1 / 2 : ℝ) *
        (momentDimension L s) ^ (1 / 2 - 1 / p)) := by
      rw [← Real.rpow_add he]
      congr 2
      ring
    _ = (s * Real.sqrt (momentDimension L s)) *
        (momentDimension L s) ^ (1 / 2 - 1 / p) := by rw [Real.sqrt_eq_rpow]; ring
    _ = _ := by rw [momentDimension_scale hL.le hs]

theorem momentDimension_power_square {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (p : ℝ) :
    (s * (momentDimension L s) ^ (1 - 1 / p)) ^ 2 =
      L ^ 2 * (momentDimension L s) ^ (1 - 2 / p) := by
  rw [momentDimension_power hL hs, mul_pow,
    ← Real.rpow_mul_natCast (momentDimension_pos hL hs).le]
  congr 2
  norm_num
  ring

theorem momentDimension_scale_square {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    s ^ 2 = L ^ 2 / momentDimension L s := by
  unfold momentDimension
  field_simp

theorem effective_dimension_convex_identity {L s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (D p δ : ℝ) (T : ℕ) :
    D * (heavyDimensionTerm L s p T + heavyConfidenceTerm s p δ T) =
      D * L / (T : ℝ) ^ (1 - 1 / p) *
        ((momentDimension L s) ^ (1 / 2 - 1 / p) +
          (confidenceLog δ) ^ (1 - 1 / p) / Real.sqrt (momentDimension L s)) := by
  let e := momentDimension L s
  have hfirst := momentDimension_power hL hs p
  have hscale := momentDimension_inverse_scale hL hs
  change s * e ^ (1 - 1 / p) = L * e ^ (1 / 2 - 1 / p) at hfirst
  change s = L / Real.sqrt e at hscale
  change D * (s * e ^ (1 - 1 / p) / (T : ℝ) ^ (1 - 1 / p) +
    s * (confidenceLog δ) ^ (1 - 1 / p) / (T : ℝ) ^ (1 - 1 / p)) =
    D * L / (T : ℝ) ^ (1 - 1 / p) *
      (e ^ (1 / 2 - 1 / p) + (confidenceLog δ) ^ (1 - 1 / p) / Real.sqrt e)
  rw [hfirst, hscale]
  dsimp only [e]
  ring

theorem effective_dimension_strong_identity {L s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (μ p δ : ℝ) (T : ℕ) :
    heavySquareScale L s p δ T / μ =
      L ^ 2 / (μ * (T : ℝ) ^ (2 * (1 - 1 / p))) *
        ((momentDimension L s) ^ (1 - 2 / p) +
          (confidenceLog δ) ^ (2 * (1 - 1 / p)) / momentDimension L s) := by
  let e := momentDimension L s
  have hfirst := momentDimension_power_square hL hs p
  have hscale := momentDimension_scale_square hL hs
  change (s * e ^ (1 - 1 / p)) ^ 2 = L ^ 2 * e ^ (1 - 2 / p) at hfirst
  change s ^ 2 = L ^ 2 / e at hscale
  change (((s * e ^ (1 - 1 / p)) ^ 2 + s ^ 2 * (confidenceLog δ) ^ (2 * (1 - 1 / p))) /
    (T : ℝ) ^ (2 * (1 - 1 / p))) / μ = _
  rw [hfirst, hscale]
  dsimp only [e]
  ring

theorem confidence_coefficient_gain {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (q : ℝ) :
    (s * (momentDimension L s) ^ (q / 2)) / s = (momentDimension L s) ^ (q / 2) ∧
    (s * (momentDimension L s) ^ (q / 2)) ^ 2 / s ^ 2 = (momentDimension L s) ^ q := by
  constructor
  · field_simp
  · rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hs.ne'),
      ← Real.rpow_mul_natCast (momentDimension_pos hL hs).le]
    congr 1
    norm_num

theorem statisticalAmplitude_variance_endpoint {L s δ : ℝ} (hL : 0 < L) (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (T : ℕ) :
    (L + s * Real.sqrt (confidenceLog δ)) / Real.sqrt T ≤ statisticalAmplitude L s 2 δ T ∧
    statisticalAmplitude L s 2 δ T ≤ 2 * ((L + s * Real.sqrt (confidenceLog δ)) / Real.sqrt T) := by
  let e := momentDimension L s
  let ell := confidenceLog δ
  have he : 0 < e := momentDimension_pos hL hs
  have hell : 0 ≤ ell := (confidenceLog_pos hδ hδ1).le
  have hscale : s * Real.sqrt e = L := momentDimension_scale hL.le hs
  have hlow : Real.sqrt ell ≤ Real.sqrt (e + ell) := Real.sqrt_le_sqrt (by linarith)
  have hhigh : Real.sqrt (e + ell) ≤ Real.sqrt e + Real.sqrt ell := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt he.le, Real.sq_sqrt hell,
        mul_nonneg (Real.sqrt_nonneg e) (Real.sqrt_nonneg ell)]
  have heq : statisticalAmplitude L s 2 δ T = (L + s * Real.sqrt (e + ell)) / Real.sqrt T := by
    unfold statisticalAmplitude
    norm_num
    rw [← Real.sqrt_eq_rpow]
    change L / Real.sqrt T + s * Real.sqrt ((e + ell) / T) = _
    rw [Real.sqrt_div (add_nonneg he.le hell)]
    dsimp only [e, ell, momentDimension, confidenceLog]
    ring
  rw [heq]
  constructor
  · exact div_le_div_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left hlow hs.le) L) (Real.sqrt_nonneg _)
  · have hh := mul_le_mul_of_nonneg_left hhigh hs.le
    have hnum : L + s * Real.sqrt (e + ell) ≤ 2 * (L + s * Real.sqrt ell) := by
      nlinarith [mul_nonneg hs.le (Real.sqrt_nonneg ell)]
    convert div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg (T : ℝ)) using 1 <;> ring

end HeavyTail
