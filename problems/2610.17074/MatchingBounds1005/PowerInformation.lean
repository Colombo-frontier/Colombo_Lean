import MatchingBounds1005.AnalyticFamily

/-! Scalar information-budget arithmetic with the exact source powers.
The inputs are bounds on actual dimension, phase count, signal weights,
cyclic angle, and bad-event mass; no KL or transcript property is assumed. -/
noncomputable section

namespace MatchingBounds1005.PowerInformation

theorem inverse_fourth_bound {t K : ℝ} (ht : 0 < t) (hK : 1 / t ^ 42 ≤ K) :
    1 / K ^ 4 ≤ t ^ 168 := by
  have hKpos : 0 < K := (by positivity : (0 : ℝ) < 1 / t ^ 42).trans_le hK
  have hm := (div_le_iff₀ (pow_pos ht 42)).mp hK
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm 4
  apply (div_le_iff₀ (pow_pos hKpos 4)).mpr
  convert hp using 1 <;> ring

theorem source_budget_bound {t d N w₃ w₄ θ ζ D M W₃ W₄ B C₃ C₄ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hW3 : 0 ≤ W₃) (hW4 : 0 ≤ W₄)
    (hB : 0 ≤ B) (hC3 : 0 ≤ C₃) (hC4 : 0 ≤ C₄) (hζ : 0 ≤ ζ)
    (hdim : d ≤ D / t ^ 47) (hphase : N ≤ M / t ^ 4)
    (hw3 : |w₃| ≤ W₃ * t) (hw4 : |w₄| ≤ W₄)
    (hangle : θ ^ 2 ≤ B * t ^ 37) (hbad : ζ ≤ t ^ 168) :
    C₃ * d * N ^ 2 * w₃ ^ 2 * θ ^ 4 / t ^ 18 +
      C₄ * d * N ^ 2 * w₄ ^ 2 * θ ^ 6 / t ^ 24 +
      ζ * (C₃ * d * N ^ 2 * w₃ ^ 2 / t ^ 18 + C₄ * d * N ^ 2 * w₄ ^ 2 / t ^ 24) ≤
    (C₃ * D * M ^ 2 * W₃ ^ 2 * (B ^ 2 + 1) +
      C₄ * D * M ^ 2 * W₄ ^ 2 * (B ^ 3 + 1)) * t ^ 3 := by
  have hn2 : N ^ 2 ≤ M ^ 2 / t ^ 8 := by
    have h := pow_le_pow_left₀ hN hphase 2
    simpa only [div_pow, ← pow_mul, Nat.reduceMul] using h
  have hw32 : w₃ ^ 2 ≤ W₃ ^ 2 * t ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg w₃) hw3 2
    simpa only [sq_abs, mul_pow] using h
  have hw42 : w₄ ^ 2 ≤ W₄ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg w₄) hw4 2
  have hθ4 : θ ^ 4 ≤ B ^ 2 * t ^ 74 := by
    have h := pow_le_pow_left₀ (sq_nonneg θ) hangle 2
    convert h using 1 <;> ring
  have hθ6 : θ ^ 6 ≤ B ^ 3 * t ^ 111 := by
    have h := pow_le_pow_left₀ (sq_nonneg θ) hangle 3
    convert h using 1 <;> ring
  have hg3 : C₃ * d * N ^ 2 * w₃ ^ 2 * θ ^ 4 / t ^ 18 ≤
      (C₃ * D * M ^ 2 * W₃ ^ 2 * B ^ 2) * t ^ 3 := by
    calc
      _ ≤ C₃ * (D / t ^ 47) * (M ^ 2 / t ^ 8) * (W₃ ^ 2 * t ^ 2) * (B ^ 2 * t ^ 74) / t ^ 18 := by
        gcongr
      _ = _ := by field_simp [ht.ne']; ring
  have hg4 : C₄ * d * N ^ 2 * w₄ ^ 2 * θ ^ 6 / t ^ 24 ≤
      (C₄ * D * M ^ 2 * W₄ ^ 2 * B ^ 3) * t ^ 32 := by
    calc
      _ ≤ C₄ * (D / t ^ 47) * (M ^ 2 / t ^ 8) * W₄ ^ 2 * (B ^ 3 * t ^ 111) / t ^ 24 := by
        gcongr
      _ = _ := by field_simp [ht.ne']; ring
  have hb3 : ζ * (C₃ * d * N ^ 2 * w₃ ^ 2 / t ^ 18) ≤
      (C₃ * D * M ^ 2 * W₃ ^ 2) * t ^ 97 := by
    calc
      _ ≤ t ^ 168 * (C₃ * (D / t ^ 47) * (M ^ 2 / t ^ 8) * (W₃ ^ 2 * t ^ 2) / t ^ 18) := by
        gcongr
      _ = _ := by field_simp [ht.ne']; ring
  have hb4 : ζ * (C₄ * d * N ^ 2 * w₄ ^ 2 / t ^ 24) ≤
      (C₄ * D * M ^ 2 * W₄ ^ 2) * t ^ 89 := by
    calc
      _ ≤ t ^ 168 * (C₄ * (D / t ^ 47) * (M ^ 2 / t ^ 8) * W₄ ^ 2 / t ^ 24) := by
        gcongr
      _ = _ := by field_simp [ht.ne']; ring
  have ht32 : t ^ 32 ≤ t ^ 3 := pow_le_pow_of_le_one ht.le ht1 (by omega)
  have ht97 : t ^ 97 ≤ t ^ 3 := pow_le_pow_of_le_one ht.le ht1 (by omega)
  have ht89 : t ^ 89 ≤ t ^ 3 := pow_le_pow_of_le_one ht.le ht1 (by omega)
  have hg4' := hg4.trans (mul_le_mul_of_nonneg_left ht32 (by positivity))
  have hb3' := hb3.trans (mul_le_mul_of_nonneg_left ht97 (by positivity))
  have hb4' := hb4.trans (mul_le_mul_of_nonneg_left ht89 (by positivity))
  calc
    _ = (C₃ * d * N ^ 2 * w₃ ^ 2 * θ ^ 4 / t ^ 18 +
      C₄ * d * N ^ 2 * w₄ ^ 2 * θ ^ 6 / t ^ 24) +
        (ζ * (C₃ * d * N ^ 2 * w₃ ^ 2 / t ^ 18) + ζ * (C₄ * d * N ^ 2 * w₄ ^ 2 / t ^ 24)) := by ring
    _ ≤ ((C₃ * D * M ^ 2 * W₃ ^ 2 * B ^ 2) * t ^ 3 +
      (C₄ * D * M ^ 2 * W₄ ^ 2 * B ^ 3) * t ^ 3) +
        ((C₃ * D * M ^ 2 * W₃ ^ 2) * t ^ 3 + (C₄ * D * M ^ 2 * W₄ ^ 2) * t ^ 3) :=
      add_le_add (add_le_add hg3 hg4') (add_le_add hb3' hb4')
    _ = _ := by ring

end MatchingBounds1005.PowerInformation
