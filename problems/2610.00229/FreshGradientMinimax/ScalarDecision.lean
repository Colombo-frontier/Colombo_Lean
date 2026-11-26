import FreshGradientMinimax.RealCoordinate

/-! A global success barrier from a local affine approximation and genuine
global monotonicity. The intervals are the constants in Lemma B.1. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def pathDecisionLeft (s ε q : ℝ) : ℝ := -(11 / 2 + 2 * s) * ε / q
def pathDecisionRight (s ε q : ℝ) : ℝ := -(5 / 2 + 2 * s) * ε / q
def pathDecisionInterval (s ε q : ℝ) : Set ℝ := Set.Icc (pathDecisionLeft s ε q) (pathDecisionRight s ε q)

theorem pathDecisionLeft_window {s ε q : ℝ} (hs : |s| ≤ 1) (hε : 0 < ε) (hq : 0 < q) :
    pathDecisionLeft s ε q ∈ Set.Icc (-8 * ε / q) 0 := by
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hs).1 hε.le
  have hhi := mul_le_mul_of_nonneg_right (abs_le.mp hs).2 hε.le
  constructor
  · apply (div_le_div_iff_of_pos_right hq).mpr
    nlinarith only [hhi, hε]
  · apply div_nonpos_of_nonpos_of_nonneg _ hq.le
    nlinarith only [hlo, hε]

theorem pathDecisionRight_window {s ε q : ℝ} (hs : |s| ≤ 1) (hε : 0 < ε) (hq : 0 < q) :
    pathDecisionRight s ε q ∈ Set.Icc (-8 * ε / q) 0 := by
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hs).1 hε.le
  have hhi := mul_le_mul_of_nonneg_right (abs_le.mp hs).2 hε.le
  constructor
  · apply (div_le_div_iff_of_pos_right hq).mpr
    nlinarith only [hhi, hε]
  · apply div_nonpos_of_nonpos_of_nonneg _ hq.le
    nlinarith only [hlo, hε]

theorem pathDecisionLeft_affine {q : ℝ} (hq : 0 < q) (s ε : ℝ) :
    q * pathDecisionLeft s ε q + (4 + 2 * s) * ε = -3 * ε / 2 := by
  unfold pathDecisionLeft
  field_simp
  ring

theorem pathDecisionRight_affine {q : ℝ} (hq : 0 < q) (s ε : ℝ) :
    q * pathDecisionRight s ε q + (4 + 2 * s) * ε = 3 * ε / 2 := by
  unfold pathDecisionRight
  field_simp
  ring

theorem scalar_success_interval {g : ℝ → ℝ} {s ε q : ℝ}
    (hm : Monotone g) (hs : |s| ≤ 1) (hε : 0 < ε) (hq : 0 < q)
    (ha : ∀ x ∈ Set.Icc (-8 * ε / q) 0, |g x - (q * x + (4 + 2 * s) * ε)| ≤ ε / 8)
    {x : ℝ} (hx : |g x| ≤ ε) : x ∈ pathDecisionInterval s ε q := by
  have hl := (abs_le.mp (ha _ (pathDecisionLeft_window hs hε hq))).2
  have hr := (abs_le.mp (ha _ (pathDecisionRight_window hs hε hq))).1
  rw [pathDecisionLeft_affine hq] at hl
  rw [pathDecisionRight_affine hq] at hr
  have hgl : g (pathDecisionLeft s ε q) < -ε := by linarith
  have hgr : ε < g (pathDecisionRight s ε q) := by linarith
  constructor
  · by_contra hn
    have h := hm (le_of_not_ge hn)
    linarith [(abs_le.mp hx).1]
  · by_contra hn
    have h := hm (le_of_not_ge hn)
    linarith [(abs_le.mp hx).2]

theorem pathDecisionInterval_disjoint {ε q : ℝ} (hε : 0 < ε) (hq : 0 < q) :
    Disjoint (pathDecisionInterval 1 ε q) (pathDecisionInterval (-1) ε q) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hsep : pathDecisionRight 1 ε q - pathDecisionLeft (-1) ε q = -ε / q := by
    unfold pathDecisionRight pathDecisionLeft; ring
  have hp : 0 < ε / q := div_pos hε hq
  have hn : -ε / q = -(ε / q) := by ring
  rw [hn] at hsep
  linarith [hx.2, hy.1]

theorem scalar_initial_gradient_bound {g : ℝ → ℝ} {s ε : ℝ}
    (hs : |s| ≤ 1) (hε : 0 < ε) (h0 : |g 0 - (4 + 2 * s) * ε| ≤ ε / 8) :
    |g 0| ≤ 49 / 8 * ε := by
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hs).1 hε.le
  have hhi := mul_le_mul_of_nonneg_right (abs_le.mp hs).2 hε.le
  exact abs_le.mpr ⟨by linarith [(abs_le.mp h0).1], by linarith [(abs_le.mp h0).2]⟩

end FreshGradientMinimax
