import FreshGradientMinimax.TestingObjective

/-! Actual primal-gap bounds for the clipped testing family, including the
constant 151424 from Appendix D. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem testingFunction_lower {μ R s : ℝ} (hμ : 0 < μ) (hR : 0 < R) (hs : |s| ≤ 1)
    (a b d x y : ℝ) :
    a / 2 * x ^ 2 + d * x + b * x * y - (7 * μ / 2) * y ^ 2 ≤
      testingFunction a b μ d R s x y := by
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hs).1 (clipSquare_nonneg R y)
  have hu := clipSquare_le_square hR y
  have hm : -y ^ 2 / 2 ≤ s * clipSquare R y := by linarith
  have h := mul_le_mul_of_nonneg_left hm hμ.le
  unfold testingFunction
  nlinarith only [h]

theorem testingObjective_value_lower {L μ d R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hs : |s| ≤ 1) (x : Euclid 1) :
    testingSlopeMinus L μ / 2 * (realCoord x) ^ 2 + d * realCoord x ≤
      (testingObjective L μ d R s hμ hR hκ hs).value x := by
  let y : ℝ := (L / 16) * realCoord x / (7 * μ)
  have h := testingFunction_lower hμ hR hs (L / 16) (L / 16) d (realCoord x) y
  have he : testingSlopeMinus L μ / 2 * (realCoord x) ^ 2 + d * realCoord x =
      (L / 16) / 2 * (realCoord x) ^ 2 + d * realCoord x +
        (L / 16) * realCoord x * y - (7 * μ / 2) * y ^ 2 := by
    dsimp [testingSlopeMinus, y]
    field_simp
    ring
  rw [← he] at h
  have hv := (testingObjective L μ d R s hμ hR hκ hs).le_value x (realVector y)
  change testingFunction (L / 16) (L / 16) μ d R s (realCoord x) (realCoord (realVector y)) ≤ _ at hv
  rw [realCoord_vector] at hv
  exact h.trans hv

theorem testingObjective_gap {L μ d R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hs : |s| ≤ 1) :
    (testingObjective L μ d R s hμ hR hκ hs).PrimalGapAtMost
      (d ^ 2 / (2 * testingSlopeMinus L μ)) := by
  intro x
  rw [testingObjective_value_zero]
  have hL : 0 < L := by linarith
  have hq := (testing_slopes_ordered hL hμ).1
  have h := testingObjective_value_lower (d := d) hμ hR hκ hs x
  have he := local_quadratic_gap hq d (realCoord x)
  have hn : 0 ≤ testingSlopeMinus L μ / 2 * (realCoord x + d / testingSlopeMinus L μ) ^ 2 := by positivity
  linarith

theorem testing_gap_constant {L μ ε : ℝ} (hμ : 0 < μ) (hκ : 1120 * μ ≤ L) (hε : 0 ≤ ε) :
    (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε) ^ 2 /
      (2 * testingSlopeMinus L μ) ≤ 151424 * μ * ε ^ 2 / L ^ 2 := by
  have hL : 0 < L := by linarith
  have hq := (testing_slopes_ordered hL hμ).1
  have hd := testing_offset_bounds hL hμ hκ hε
  have hd0 : 0 ≤ testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε := by linarith [hd.1]
  have hd2 : (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε) ^ 2 ≤ 169 * ε ^ 2 := by
    nlinarith only [sq_le_sq₀ hd0 (show 0 ≤ 13 * ε by positivity) |>.mpr hd.2]
  have hbase : L ^ 2 ≤ 1792 * μ * testingSlopeMinus L μ := by
    unfold testingSlopeMinus
    have he : 1792 * μ * (L / 16 + (L / 16) ^ 2 / (7 * μ)) = L ^ 2 + 112 * μ * L := by
      field_simp; ring
    rw [he]
    nlinarith [mul_pos hμ hL]
  calc
    _ ≤ 169 * ε ^ 2 / (2 * testingSlopeMinus L μ) :=
      div_le_div_of_nonneg_right hd2 (by positivity)
    _ ≤ 151424 * μ * ε ^ 2 / L ^ 2 := by
      apply (div_le_iff₀ (show 0 < 2 * testingSlopeMinus L μ by positivity)).mpr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
      have h := mul_le_mul_of_nonneg_right hbase (sq_nonneg ε)
      nlinarith only [h]

theorem testingObjective_gap_rate {L μ ε R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hε : 0 ≤ ε) (hs : |s| ≤ 1) :
    (testingObjective L μ (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε)
      R s hμ hR hκ hs).PrimalGapAtMost (151424 * μ * ε ^ 2 / L ^ 2) := by
  intro x
  exact (testingObjective_gap hμ hR hκ hs x).trans (testing_gap_constant hμ hκ hε)

end FreshGradientMinimax
