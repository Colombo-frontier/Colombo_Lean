import FreshGradientMinimax.AcceleratedHidingThreshold

/-! The hiding event has a strict margin inside every flat region. The
factor two allows the event to persist in a neighborhood of the query. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem accelerated_small_linear_edge_margin (n : ℕ) {k : ℕ} (hk : 0 < k) {a b s t : ℝ}
    (ha : |a| ≤ 1 + Real.sqrt (robinC (n + 2))) (hb : |b| ≤ 1 + Real.sqrt (robinC (n + 2)))
    (hs : |s| ≤ 2 * acceleratedHidingThreshold n k) (ht : |t| ≤ 2 * acceleratedHidingThreshold n k) :
    |a * s + b * t| ≤ acceleratedThreshold n k := by
  have hc : 0 ≤ 1 + Real.sqrt (robinC (n + 2)) := by positivity
  have h1 := mul_le_mul ha hs (abs_nonneg s) hc
  have h2 := mul_le_mul hb ht (abs_nonneg t) hc
  have h := abs_add_le (a * s) (b * t)
  rw [abs_mul, abs_mul] at h
  nlinarith only [h, h1, h2, acceleratedHidingThreshold_identity n k, acceleratedThreshold_pos n hk]

theorem accelerated_hidden_primal_flat_margin (n : ℕ) {k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu : |u| ≤ 2 * acceleratedHidingThreshold n k) :
    flatEdge (acceleratedThreshold n k) (smoothClip 2 u) = 0 := by
  apply flatEdge_flat (acceleratedThreshold_pos n hk).le
  apply (smoothClip_le_abs (by norm_num : (0 : ℝ) < 2) u).trans
  apply hu.trans
  linarith only [acceleratedHidingThreshold_le_eighth n hk, acceleratedThreshold_pos n hk]

theorem accelerated_hidden_nonlinear_flat_margin (n : ℕ) {k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu : |u| ≤ 2 * acceleratedHidingThreshold n k) (v : ℝ) :
    coreLinkTerm (smoothClip 2 u) (smoothClip 2 v) = 0 := by
  have hc : |smoothClip 2 u| ≤ 1 / 2 :=
    (smoothClip_le_abs (by norm_num : (0 : ℝ) < 2) u).trans
      (hu.trans (by linarith only [acceleratedHidingThreshold_lt_quarter n hk]))
  have h := coreGate_flat hc
  simp only [coreLinkTerm, h.1, h.2, zero_mul, sub_self]

theorem robin_edge_coefficient_bounds (n : ℕ) :
    |(Real.sqrt (n + 2 : ℕ))⁻¹| ≤ 1 + Real.sqrt (robinC (n + 2)) ∧
    |Real.sqrt (robinC (n + 2))| ≤ 1 + Real.sqrt (robinC (n + 2)) ∧
    |Real.sqrt (robinC (n + 2)) / 2| ≤ 1 + Real.sqrt (robinC (n + 2)) ∧
    |(1 : ℝ)| ≤ 1 + Real.sqrt (robinC (n + 2)) := by
  have hs : (1 : ℝ) ≤ Real.sqrt (n + 2 : ℕ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have hi : (Real.sqrt (n + 2 : ℕ))⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith only [hs])).mpr hs
  have hc := Real.sqrt_nonneg (robinC (n + 2))
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), abs_of_nonneg hc,
    abs_of_nonneg (div_nonneg hc (by norm_num)), abs_one]
  constructor
  · linarith only [hi, hc]
  constructor
  · linarith
  constructor <;> linarith

end FreshGradientMinimax
