import Mathlib.Tactic

/-! Exact scalar accounting for additions and full-column revelations. -/
noncomputable section
namespace Bilevel.ProjectionEnergy

def envelope (q r : ℝ) : ℝ := q / (1 - r * q)

theorem query_step (q r b : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (hcap : r * (q + b) < 1) : envelope q r + b ≤ envelope (q + b) r := by
  have hd : 0 < 1 - r * q := by nlinarith [mul_nonneg hr hb]
  have hd' : 0 < 1 - r * (q + b) := by linarith
  have he : envelope q r + b = (q + b * (1 - r * q)) / (1 - r * q) := by
    unfold envelope
    field_simp
  rw [he, envelope]
  apply (div_le_div_iff₀ hd hd').mpr
  have hp := mul_nonneg (mul_nonneg hb hr)
    (add_nonneg hq (mul_nonneg (add_nonneg hq hb) hd.le))
  nlinarith only [hp]

theorem before_revelation (q r : ℝ) (hq : 0 ≤ q) (hcap : (r + 1) * q < 1) :
    0 < 1 - r * q ∧ envelope q r < 1 := by
  have hd : 0 < 1 - r * q := by nlinarith
  refine ⟨hd, ?_⟩
  exact (div_lt_one hd).mpr (by nlinarith)

theorem revelation_step (q r : ℝ) (hq : 0 ≤ q) (hcap : (r + 1) * q < 1) :
    envelope q r / (1 - envelope q r) = envelope q (r + 1) := by
  have h := before_revelation q r hq hcap
  have hd : 1 - r * q ≠ 0 := h.1.ne'
  have hd' : 1 - (r + 1) * q ≠ 0 := by linarith
  have he : 1 - envelope q r = (1 - (r + 1) * q) / (1 - r * q) := by
    unfold envelope
    field_simp
    ring
  rw [he]
  unfold envelope
  field_simp [hd, hd']

theorem revelation_monotone (x y : ℝ) (hxy : x ≤ y) (hy : y < 1) :
    x / (1 - x) ≤ y / (1 - y) := by
  have hx : 0 < 1 - x := by linarith
  have hy' : 0 < 1 - y := by linarith
  apply (div_le_div_iff₀ hx hy').mpr
  nlinarith

theorem envelope_le_twice (q r : ℝ) (hq : 0 ≤ q) (hcap : r * q ≤ 1 / 2) :
    envelope q r ≤ 2 * q := by
  have hd : 0 < 1 - r * q := by linarith
  apply (div_le_iff₀ hd).mpr
  have hp := mul_nonneg hq (show 0 ≤ 1 / 2 - r * q by linarith)
  nlinarith

end Bilevel.ProjectionEnergy
