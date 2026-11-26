import NCConcave16991.Rates
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Integer effective component counts in Appendix F.2 -/

noncomputable section

namespace NCConcave16991.Replication

def effectiveScale (n : ℕ) (B b : ℝ) : ℝ := min (n : ℝ) ((B / b) ^ 4)
def effectiveCount (n : ℕ) (B b : ℝ) : ℕ := ⌊effectiveScale n B b⌋₊

theorem effectiveScale_one_le {n : ℕ} (hn : 0 < n) {B b : ℝ}
    (hb : 0 < b) (hB : b ≤ B) : 1 ≤ effectiveScale n B b := by
  unfold effectiveScale
  apply le_min
  · exact_mod_cast hn
  · have hratio : 1 ≤ B / b := (le_div_iff₀ hb).2 (by simpa using hB)
    exact one_le_pow₀ hratio

theorem effectiveCount_bounds {n : ℕ} (hn : 0 < n) {B b : ℝ}
    (hb : 0 < b) (hB : b ≤ B) :
    0 < effectiveCount n B b ∧ effectiveCount n B b ≤ n ∧
      (effectiveCount n B b : ℝ) ≤ (B / b) ^ 4 ∧
      effectiveScale n B b ≤ 2 * (effectiveCount n B b : ℝ) := by
  have hX := effectiveScale_one_le hn hb hB
  have hpos : 1 ≤ effectiveCount n B b := Nat.le_floor (by simpa only [Nat.cast_one] using hX)
  have hfloor := Nat.floor_le (show 0 ≤ effectiveScale n B b by linarith)
  have hfloor' : (effectiveCount n B b : ℝ) ≤ effectiveScale n B b := hfloor
  have hupper : effectiveCount n B b ≤ n :=
    Nat.floor_le_of_le (show effectiveScale n B b ≤ (n : ℝ) from min_le_left _ _)
  have hlt := Nat.lt_floor_add_one (effectiveScale n B b)
  have hposR : (1 : ℝ) ≤ effectiveCount n B b := by exact_mod_cast hpos
  refine ⟨hpos, hupper, hfloor'.trans (min_le_right _ _), ?_⟩
  change effectiveScale n B b < (effectiveCount n B b : ℝ) + 1 at hlt
  linarith

theorem effectiveCount_quarter_bound {n : ℕ} (hn : 0 < n) {B b : ℝ}
    (hb : 0 < b) (hB : b ≤ B) :
    (effectiveCount n B b : ℝ) ^ (1 / 4 : ℝ) ≤ B / b := by
  have hratio : 0 ≤ B / b := div_nonneg (hb.le.trans hB) hb.le
  have h := Real.rpow_le_rpow (Nat.cast_nonneg (effectiveCount n B b))
    (effectiveCount_bounds hn hb hB).2.2.1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have he : ((B / b) ^ 4) ^ (1 / 4 : ℝ) = B / b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
    norm_num
  rwa [he] at h

theorem effectiveScale_three_quarters {n : ℕ} (hn : 0 < n) {B b : ℝ}
    (hb : 0 < b) (hB : b ≤ B) :
    effectiveScale n B b ^ (3 / 4 : ℝ) ≤
      2 * (effectiveCount n B b : ℝ) ^ (3 / 4 : ℝ) := by
  have hbounds := effectiveCount_bounds hn hb hB
  have hx := effectiveScale_one_le hn hb hB
  have hr := Real.rpow_le_rpow (show 0 ≤ effectiveScale n B b by linarith)
    hbounds.2.2.2 (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)] at hr
  have ht : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (3 / 4 : ℝ) ≤ 1) using 1 <;> norm_num
  exact hr.trans (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Rounding loses at most the universal factor 2*b^3. This slightly relaxed
constant avoids carrying an unnecessary fractional power of 2. -/
theorem diameterLower_le_effectiveCount {n : ℕ} (hn : 0 < n) {B b : ℝ}
    (hb : 1 ≤ b) (hB : b ≤ B) :
    diameterLower (n : ℝ) B ≤
      2 * b ^ 3 * B * (effectiveCount n B b : ℝ) ^ (3 / 4 : ℝ) := by
  have hbpos : 0 < b := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hpow := effectiveScale_three_quarters hn hbpos hB
  have hratio : 0 ≤ B / b := div_nonneg hB0 hbpos.le
  by_cases hcase : (n : ℝ) ≤ (B / b) ^ 4
  · rw [effectiveScale, min_eq_left hcase] at hpow
    have h1 := mul_le_mul_of_nonneg_left hpow hB0
    have h2 := mul_le_mul_of_nonneg_right hb3
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB0)
        (Real.rpow_nonneg (Nat.cast_nonneg (effectiveCount n B b)) (3 / 4 : ℝ)))
    have hmin := min_le_right (B ^ 4) ((n : ℝ) ^ (3 / 4 : ℝ) * B)
    unfold diameterLower
    nlinarith only [h1, h2, hmin]
  · rw [effectiveScale, min_eq_right (le_of_not_ge hcase)] at hpow
    have he : ((B / b) ^ 4) ^ (3 / 4 : ℝ) = (B / b) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
      norm_num [Real.rpow_natCast]
    rw [he] at hpow
    have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg (pow_nonneg hbpos.le 3) hB0)
    have hid : b ^ 3 * B * (B / b) ^ 3 = B ^ 4 := by
      field_simp [hbpos.ne']
      <;> ring
    rw [hid] at h1
    exact (min_le_left _ _).trans (by nlinarith only [h1])

end NCConcave16991.Replication
