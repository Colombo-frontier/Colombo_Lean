import Bilevel.ProjectionTrace

/-! Uniform budget bounds for every prefix of the actual energy trace. -/
noncomputable section
namespace Bilevel.ProjectionTrace
open ProjectionEnergy

theorem envelope_mono (a A r R : ℝ) (ha : 0 ≤ a) (hA : a ≤ A)
    (hr : 0 ≤ r) (hR : r ≤ R) (hcap : R*A < 1) : envelope a r ≤ envelope A R := by
  have hRA : r*a ≤ R*A := mul_le_mul hR hA ha (by linarith)
  have hd : 0 < 1-r*a := by linarith
  have hD : 0 < 1-R*A := by linarith
  apply (div_le_div_iff₀ hd hD).mpr
  have hh := mul_nonneg (show 0 ≤ R-r by linarith) (mul_nonneg ha (by linarith : 0 ≤ A))
  nlinarith

theorem counts_product_le {b : ℝ} (hb : 0 ≤ b) {q r M R : ℕ}
    (hq : q ≤ M) (hr : r ≤ R) : (r : ℝ) * ((q : ℝ)*b) ≤ (R : ℝ)*((M : ℝ)*b) := by
  exact mul_le_mul (Nat.cast_le.mpr hr) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq) hb)
    (mul_nonneg (Nat.cast_nonneg q) hb) (Nat.cast_nonneg R)

theorem bounded_counts {b : ℝ} (hb : 0 ≤ b) {q r M R : ℕ} {e : ℝ}
    (h : Trace b q r e) (hq : q ≤ M) (hr : r ≤ R)
    (hcap : (R : ℝ)*((M : ℝ)*b) < 1) : e ≤ envelope ((M : ℝ)*b) R := by
  have hc := counts_product_le hb hq hr
  exact (envelope_bound hb h (lt_of_le_of_lt hc hcap)).trans
    (envelope_mono _ _ _ _ (mul_nonneg (Nat.cast_nonneg q) hb)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq) hb)
      (Nat.cast_nonneg r) (Nat.cast_le.mpr hr) hcap)

theorem before_next_reveal {b : ℝ} (hb : 0 ≤ b) {q r M R : ℕ} {e : ℝ}
    (h : Trace b q r e) (hq : q ≤ M) (hr : r+1 ≤ R)
    (hcap : (R : ℝ)*((M : ℝ)*b) < 1) : e < 1 := by
  have hc := counts_product_le hb hq hr
  have hc' : ((r : ℝ)+1)*((q : ℝ)*b) < 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using lt_of_le_of_lt hc hcap
  have ht := envelope_bound hb h (lt_of_le_of_lt (counts_product_le hb hq (by omega : r ≤ R)) hcap)
  exact ht.trans_lt (before_revelation _ _ (mul_nonneg (Nat.cast_nonneg q) hb) hc').2

end Bilevel.ProjectionTrace
