import FreshGradientMinimax.AcceleratedMaximizerBounds
import FreshGradientMinimax.CoreLinkTermDerivative

/-! The original hiding threshold tau. Small hidden coordinates make
the actual flat-Huber edges, primal penalties and outgoing gates flat. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedHidingThreshold (n k : ℕ) : ℝ :=
  acceleratedThreshold n k / (8 * (1 + Real.sqrt (robinC (n + 2))))

theorem acceleratedThreshold_le_ridge (n : ℕ) {k : ℕ} (hk : 0 < k) :
    acceleratedThreshold n k ≤ primalRidgeConstant := by
  have hN : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hN2 : (1 : ℝ) ≤ (n + 2 : ℕ) ^ 2 := by nlinarith only [hN]
  have hM : (1 : ℝ) ≤ Real.sqrt (k * (n + 3) : ℕ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ k * (n + 3) by nlinarith only [hk]))
  have hp := mul_le_mul hN2 hM (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ) ^ 2)
  have hD : (1 : ℝ) ≤ 10 ^ 8 * (n + 2 : ℕ) ^ 2 * Real.sqrt (k * (n + 3) : ℕ) := by nlinarith only [hp]
  unfold acceleratedThreshold
  apply (div_le_iff₀ (by linarith only [hD])).mpr
  have h := mul_le_mul_of_nonneg_left hD primalRidgeConstant_pos.le
  simpa only [mul_one] using h

theorem acceleratedThreshold_le_small (n : ℕ) {k : ℕ} (hk : 0 < k) : acceleratedThreshold n k ≤ 1 / 100 := by
  have hη : primalRidgeConstant ≤ 1 / 100 := by
    unfold primalRidgeConstant
    linarith only [primalBarrierConstant_le_one]
  exact (acceleratedThreshold_le_ridge n hk).trans hη

theorem acceleratedHidingThreshold_pos (n : ℕ) {k : ℕ} (hk : 0 < k) : 0 < acceleratedHidingThreshold n k :=
  div_pos (acceleratedThreshold_pos n hk) (by have := Real.sqrt_nonneg (robinC (n + 2)); positivity)

theorem acceleratedHidingThreshold_identity (n k : ℕ) :
    (1 + Real.sqrt (robinC (n + 2))) * acceleratedHidingThreshold n k = acceleratedThreshold n k / 8 := by
  have hs : 0 < 1 + Real.sqrt (robinC (n + 2)) := by have := Real.sqrt_nonneg (robinC (n + 2)); positivity
  unfold acceleratedHidingThreshold
  field_simp [hs.ne']
  ring

theorem acceleratedHidingThreshold_le_eighth (n : ℕ) {k : ℕ} (hk : 0 < k) :
    acceleratedHidingThreshold n k ≤ acceleratedThreshold n k / 8 := by
  have h := acceleratedHidingThreshold_identity n k
  have hp := mul_nonneg (Real.sqrt_nonneg (robinC (n + 2))) (acceleratedHidingThreshold_pos n hk).le
  nlinarith only [h, hp]

theorem acceleratedHidingThreshold_le_flat (n : ℕ) {k : ℕ} (hk : 0 < k) :
    acceleratedHidingThreshold n k ≤ acceleratedThreshold n k := by
  linarith only [acceleratedHidingThreshold_le_eighth n hk, acceleratedThreshold_pos n hk]

theorem acceleratedHidingThreshold_lt_quarter (n : ℕ) {k : ℕ} (hk : 0 < k) : acceleratedHidingThreshold n k < 1 / 4 := by
  linarith only [acceleratedHidingThreshold_le_eighth n hk, acceleratedThreshold_le_small n hk]

theorem accelerated_small_linear_edge (n : ℕ) {k : ℕ} (hk : 0 < k) {a b s t : ℝ}
    (ha : |a| ≤ 1 + Real.sqrt (robinC (n + 2))) (hb : |b| ≤ 1 + Real.sqrt (robinC (n + 2)))
    (hs : |s| ≤ acceleratedHidingThreshold n k) (ht : |t| ≤ acceleratedHidingThreshold n k) :
    |a * s + b * t| ≤ acceleratedThreshold n k := by
  have hc : 0 ≤ 1 + Real.sqrt (robinC (n + 2)) := by positivity
  have h1 := mul_le_mul ha hs (abs_nonneg s) hc
  have h2 := mul_le_mul hb ht (abs_nonneg t) hc
  have h := abs_add_le (a * s) (b * t)
  rw [abs_mul, abs_mul] at h
  nlinarith only [h, h1, h2, acceleratedHidingThreshold_identity n k, acceleratedThreshold_pos n hk]

theorem accelerated_hidden_edge_flat (n : ℕ) {k : ℕ} (hk : 0 < k) {a b s t : ℝ}
    (ha : |a| ≤ 1 + Real.sqrt (robinC (n + 2))) (hb : |b| ≤ 1 + Real.sqrt (robinC (n + 2)))
    (hs : |s| ≤ acceleratedHidingThreshold n k) (ht : |t| ≤ acceleratedHidingThreshold n k) :
    boundedFlatEdge (acceleratedThreshold n k) 1000 (a * s + b * t) = 0 ∧
      boundedFlatSlope (acceleratedThreshold n k) 1000 (a * s + b * t) = 0 := by
  have h := accelerated_small_linear_edge n hk ha hb hs ht
  exact ⟨boundedFlatEdge_flat (acceleratedThreshold_pos n hk).le (by norm_num) h,
    boundedFlatSlope_flat (acceleratedThreshold_pos n hk).le (by norm_num) h⟩

theorem accelerated_hidden_primal_flat (n : ℕ) {k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu : |u| ≤ acceleratedHidingThreshold n k) :
    flatEdge (acceleratedThreshold n k) (smoothClip 2 u) = 0 ∧
      flatEdgeSlope (acceleratedThreshold n k) (smoothClip 2 u) = 0 := by
  have hc := (smoothClip_le_abs (by norm_num : (0 : ℝ) < 2) u).trans (hu.trans (acceleratedHidingThreshold_le_flat n hk))
  exact ⟨flatEdge_flat (acceleratedThreshold_pos n hk).le hc, flatEdgeSlope_flat (acceleratedThreshold_pos n hk).le hc⟩

theorem accelerated_hidden_nonlinear_flat (n : ℕ) {k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu : |u| ≤ acceleratedHidingThreshold n k) (v : ℝ) :
    coreLinkTerm (smoothClip 2 u) (smoothClip 2 v) = 0 ∧
      coreLinkTermD1 (smoothClip 2 u) (smoothClip 2 v) = 0 ∧
      coreLinkTermD2 (smoothClip 2 u) (smoothClip 2 v) = 0 := by
  have hc : |smoothClip 2 u| ≤ 1 / 2 :=
    (smoothClip_le_abs (by norm_num : (0 : ℝ) < 2) u).trans
      (hu.trans (by linarith only [acceleratedHidingThreshold_lt_quarter n hk]))
  refine ⟨?_, coreLinkTermD_flat hc _⟩
  have h := coreGate_flat hc
  simp only [coreLinkTerm, h.1, h.2, zero_mul, sub_self]

end FreshGradientMinimax
