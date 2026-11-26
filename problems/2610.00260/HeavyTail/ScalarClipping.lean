import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Scalar clipping estimate

This proves manuscript Lemma `lem:mixed-scalar` for every real exponent
`1 < p ≤ 2`. The explicit universal constant is 100 (hence 256 also works).
-/

namespace HeavyTail

def clip (x : ℝ) : ℝ := max (-1) (min x 1)

lemma clip_mem (x : ℝ) : -1 ≤ clip x ∧ clip x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

lemma clip_eq_self {x : ℝ} (hx : |x| ≤ 1) : clip x = x := by
  rcases abs_le.mp hx with ⟨hl, hr⟩
  simp [clip, min_eq_left hr, max_eq_right hl]

private lemma small_square_le_moment {u p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hu : |u| ≤ 1) : u ^ 2 ≤ |u| ^ p := by
  have h := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg u) hu (by linarith : 0 ≤ p) hp2
  simpa only [Real.rpow_two, sq_abs] using h

private lemma abs_le_moment_add_one {u p : ℝ} (hp : 1 < p) : |u| ≤ |u| ^ p + 1 := by
  by_cases hu : |u| ≤ 1
  · have := Real.rpow_nonneg (abs_nonneg u) p
    linarith
  · have := Real.self_le_rpow_of_one_le (le_of_not_ge hu) (le_of_lt hp)
    linarith

private lemma abs_sum_le_moment {u v p : ℝ} (hp : 1 < p) :
    |u + v| ≤ |u| ^ p + v ^ 2 + 2 := by
  have hu := abs_le_moment_add_one (u := u) hp
  have hv : |v| ≤ v ^ 2 + 1 := by nlinarith [sq_nonneg (|v| - 1), sq_abs v]
  linarith [abs_add u v]

private lemma sign_mul_abs (ε x : ℝ) (hε : ε = -1 ∨ ε = 1) : |ε * x| = |x| := by
  rcases hε with rfl | rfl <;> simp

private lemma exp_two_le_nine : Real.exp 2 ≤ 9 := by
  have h : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hpos := Real.exp_pos 1
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  nlinarith

private lemma small_t_estimate {t u v p ε : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hε : ε = -1 ∨ ε = 1) (ht : |t| ≤ 1 / 2) :
    Real.exp (ε * (clip (t + u + v) - t)) ≤
      1 + ε * (u + v) + 100 * (|u| ^ p + v ^ 2) := by
  let H := |u| ^ p + v ^ 2
  have hpow := Real.rpow_nonneg (abs_nonneg u) p
  have hH : 0 ≤ H := by dsimp [H]; positivity
  by_cases hsmall : H ≤ 1 / 8
  · have hu : |u| ≤ 1 := by
      by_contra hh
      have hlarge := Real.self_le_rpow_of_one_le (le_of_not_ge hh) (le_of_lt hp)
      dsimp [H] at hsmall
      nlinarith [sq_nonneg v]
    have hu2 := small_square_le_moment hp hp2 hu
    have hz2 : (u + v) ^ 2 ≤ 2 * H := by
      dsimp [H]
      nlinarith [sq_nonneg (u - v)]
    have hz : |u + v| ≤ 1 / 2 := by
      have hzsq : |u + v| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [sq_abs]
        have hb := hz2.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2))
        norm_num at hb ⊢
        exact hb
      nlinarith only [hzsq, abs_nonneg (u + v)]
    have htuv : |t + u + v| ≤ 1 := by
      have htri := abs_add t (u + v)
      rw [← add_assoc] at htri
      linarith
    rw [clip_eq_self htuv]
    have he : |Real.exp (ε * (u + v)) - 1 - ε * (u + v)| ≤ (u + v) ^ 2 := by
      have he := Real.abs_exp_sub_one_sub_id_le (show |ε * (u + v)| ≤ 1 by
        rw [sign_mul_abs ε _ hε]; linarith)
      have hsq : (ε * (u + v)) ^ 2 = (u + v) ^ 2 := by
        rcases hε with rfl | rfl <;> simp only [neg_one_mul, neg_sq, one_mul]
      simpa only [hsq] using he
    have he' := (abs_le.mp he).2
    have hrew : ε * (t + u + v - t) = ε * (u + v) := by ring
    rw [hrew]
    change Real.exp (ε * (u + v)) ≤ 1 + ε * (u + v) + 100 * H
    nlinarith
  · have hc := clip_mem (t + u + v)
    have hexp : Real.exp (ε * (clip (t + u + v) - t)) ≤ 9 := by
      apply le_trans (Real.exp_le_exp.mpr (show ε * (clip (t + u + v) - t) ≤ 2 by
        rcases abs_le.mp ht with ⟨htl, htr⟩
        rcases hε with rfl | rfl <;> nlinarith)) exp_two_le_nine
    have hlinear : -(ε * (u + v)) ≤ |u + v| := by
      rcases hε with rfl | rfl <;> simp only [neg_one_mul, one_mul, neg_neg]
      · exact le_abs_self _
      · exact neg_le_abs _
    have hsum := abs_sum_le_moment (u := u) (v := v) hp
    change Real.exp (ε * (clip (t + u + v) - t)) ≤ 1 + ε * (u + v) + 100 * H
    change |u + v| ≤ H + 2 at hsum
    have hlarge : 1 / 8 < H := lt_of_not_ge hsmall
    have hlinear' : -(H + 2) ≤ ε * (u + v) := by
      exact neg_le.mp (hlinear.trans hsum)
    have hlarge' : (10 : ℝ) ≤ 99 * H := by
      have hh := mul_le_mul_of_nonneg_left hlarge.le (by norm_num : (0 : ℝ) ≤ 99)
      exact le_trans (by norm_num) hh
    calc
      _ ≤ 9 := hexp
      _ ≤ 99 * H - 1 := by linarith only [hlarge']
      _ = 1 + (-(H + 2)) + 100 * H := by ring
      _ ≤ 1 + ε * (u + v) + 100 * H := by gcongr

/-- Manuscript scalar clipping inequality, with an explicit absolute constant. -/
theorem mixed_scalar {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (t u v ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Real.exp (ε * (clip (t + u + v) - t)) ≤
      1 + ε * (u + v) + 100 * Real.exp (2 * |t|) *
        (|u| ^ p + v ^ 2 + if 1 / 2 < |t| then t ^ 2 else 0) := by
  have hpow := Real.rpow_nonneg (abs_nonneg u) p
  have he1 : 1 ≤ Real.exp (2 * |t|) := Real.one_le_exp (by positivity)
  by_cases ht : |t| ≤ 1 / 2
  · rw [if_neg (not_lt.mpr ht), add_zero]
    have h := small_t_estimate (u := u) (v := v) hp hp2 hε ht
    have hmul := mul_le_mul_of_nonneg_right he1 (show 0 ≤ 100 * (|u| ^ p + v ^ 2) by positivity)
    nlinarith
  · rw [if_pos (lt_of_not_ge ht)]
    have ht2 : 1 / 4 < t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have hc := clip_mem (t + u + v)
    have hx : ε * (clip (t + u + v) - t) ≤ 1 + |t| := by
      rcases hε with rfl | rfl <;> nlinarith [le_abs_self t, neg_le_abs t]
    have hexp : Real.exp (ε * (clip (t + u + v) - t)) ≤ 3 * Real.exp (2 * |t|) := by
      calc
        _ ≤ Real.exp (1 + |t|) := Real.exp_le_exp.mpr hx
        _ = Real.exp 1 * Real.exp |t| := Real.exp_add _ _
        _ ≤ 3 * Real.exp (2 * |t|) := by
          apply mul_le_mul
          · exact le_trans Real.exp_one_lt_d9.le (by norm_num)
          · exact Real.exp_le_exp.mpr (by linarith [abs_nonneg t])
          · exact Real.exp_nonneg _
          · norm_num
    have hlinear : -(ε * (u + v)) ≤ |u + v| := by
      rcases hε with rfl | rfl <;> simp only [neg_one_mul, one_mul, neg_neg]
      · exact le_abs_self _
      · exact neg_le_abs _
    have hsum := abs_sum_le_moment (u := u) (v := v) hp
    have hmulH := mul_le_mul_of_nonneg_right he1 (show 0 ≤ |u| ^ p + v ^ 2 by positivity)
    have hmult := mul_le_mul_of_nonneg_left ht2.le (Real.exp_nonneg (2 * |t|))
    nlinarith

/-- The stated manuscript constant `256` follows from the stronger estimate. -/
theorem mixed_scalar_256 {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (t u v ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Real.exp (ε * (clip (t + u + v) - t)) ≤
      1 + ε * (u + v) + 256 * Real.exp (2 * |t|) *
        (|u| ^ p + v ^ 2 + if 1 / 2 < |t| then t ^ 2 else 0) := by
  have hnonneg : 0 ≤ |u| ^ p + v ^ 2 + if 1 / 2 < |t| then t ^ 2 else 0 := by
    split_ifs <;> positivity
  calc
    _ ≤ 1 + ε * (u + v) + 100 * Real.exp (2 * |t|) *
        (|u| ^ p + v ^ 2 + if 1 / 2 < |t| then t ^ 2 else 0) :=
      mixed_scalar hp hp2 t u v ε hε
    _ ≤ _ := by gcongr <;> norm_num

end HeavyTail
