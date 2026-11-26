import FreshGradientMinimax.TestingObjective
import FreshGradientMinimax.Minimax

/-! Every true successful point of the global clipped family lies in the
corresponding affine decision interval. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem testing_stationary_sign {μ R s b x y : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hs : |s| ≤ 1) (hb : 0 < b) (hy : testingGradY b μ R s x y = 0) :
    0 ≤ x * y := by
  have hp := mul_le_mul hs (clipSquareSlope_le_abs hR y) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [one_mul, ← abs_mul] at hp
  have ht := mul_le_mul_of_nonneg_right hp (abs_nonneg y)
  rw [← abs_mul, ← sq, sq_abs] at ht
  have hu := (le_abs_self (s * clipSquareSlope R y * y)).trans ht
  have he := congrArg (fun t : ℝ => t * y) hy
  unfold testingGradY at he
  dsimp only at he
  have hmy := mul_nonneg hμ.le (sq_nonneg y)
  have hmu := mul_le_mul_of_nonneg_left hu hμ.le
  have hxy : 0 ≤ b * (x * y) := by nlinarith only [he, hmy, hmu]
  exact (mul_nonneg_iff_of_pos_left hb).mp hxy

theorem testing_stationary_dual_bound {μ R s a b d ε x y : ℝ}
    (hμ : 0 < μ) (hR : 0 < R) (hs : |s| ≤ 1) (ha : 0 ≤ a) (hb : 0 < b)
    (hd : 0 ≤ d) (hy : testingGradY b μ R s x y = 0)
    (hx : |testingGradX a b d x y| ≤ ε) : b * |y| ≤ d + ε := by
  have hxy := testing_stationary_sign hμ hR hs hb hy
  have hprod : 0 ≤ a * b * (x * y) := mul_nonneg (mul_nonneg ha hb.le) hxy
  have hsq : (b * y) ^ 2 ≤ (a * x + b * y) ^ 2 := by
    nlinarith only [hprod, sq_nonneg (a * x)]
  have hby := (sq_le_sq).mp hsq
  rw [abs_mul, abs_of_pos hb] at hby
  have he : a * x + b * y = testingGradX a b d x y - d := by unfold testingGradX; ring
  rw [he] at hby
  have ht := abs_sub (testingGradX a b d x y) d
  rw [abs_of_nonneg hd] at ht
  linarith

def testingSlope (L μ s : ℝ) : ℝ := L / 16 + (L / 16) ^ 2 / ((6 - s) * μ)

theorem testingSlope_pos {L μ s : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hs : |s| ≤ 1) :
    0 < testingSlope L μ s := by
  have hden : 0 < (6 - s) * μ := mul_pos (by linarith [(abs_le.mp hs).2]) hμ
  unfold testingSlope
  positivity

theorem testingObjective_success_subset {L μ d R s ε : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hs : |s| ≤ 1) (hd : 0 ≤ d)
    (hscale : d + ε ≤ (L / 16) * R) :
    (testingObjective L μ d R s hμ hR hκ hs).successSet ε ⊆
      {x | realCoord x ∈ successfulInterval (testingSlope L μ s) d ε} := by
  intro x hx
  let F := testingObjective L μ d R s hμ hR hκ hs
  let y := realCoord (F.dualMax x)
  have hL : 0 < L := by linarith
  have hb : 0 < L / 16 := by positivity
  have hy : testingGradY (L / 16) μ R s (realCoord x) y = 0 := by
    have h := congrArg realCoord (F.dual_gradient_zero x)
    simpa only [F, testingObjective, realCoord_vector, realCoord_zero] using h
  have hg : |testingGradX (L / 16) (L / 16) d (realCoord x) y| ≤ ε := by
    change ‖gradient F.value x‖ ≤ ε at hx
    rw [F.true_primal_gradient] at hx
    simpa only [NCObjective.primalGradient, F, testingObjective, realVector_norm] using hx
  have hby := testing_stationary_dual_bound hμ hR hs hb.le hb hd hy hg
  have hyr : |y| ≤ R := (mul_le_mul_left hb).mp (hby.trans hscale)
  rw [testingGradY, clipSquareSlope_identity hR hyr] at hy
  have hden : (6 - s) * μ ≠ 0 := ne_of_gt (mul_pos (by linarith [(abs_le.mp hs).2]) hμ)
  have hyform : y = (L / 16) * realCoord x / ((6 - s) * μ) := by
    apply (eq_div_iff hden).mpr
    nlinarith only [hy]
  change |testingSlope L μ s * realCoord x + d| ≤ ε
  have he : testingSlope L μ s * realCoord x + d =
      testingGradX (L / 16) (L / 16) d (realCoord x) y := by
    rw [hyform]
    unfold testingSlope testingGradX
    ring
  rwa [he]

theorem testingSlope_signs (L μ : ℝ) :
    testingSlope L μ 1 = testingSlopePlus L μ ∧
      testingSlope L μ (-1) = testingSlopeMinus L μ := by
  norm_num [testingSlope, testingSlopePlus, testingSlopeMinus]

theorem testingObjective_success_disjoint {L μ ε R : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hε : 0 < ε)
    (hscale : testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε + ε ≤ (L / 16) * R) :
    Disjoint
      ((testingObjective L μ (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε)
        R 1 hμ hR hκ (by norm_num)).successSet ε)
      ((testingObjective L μ (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε)
        R (-1) hμ hR hκ (by norm_num)).successSet ε) := by
  have hL : 0 < L := by linarith
  have hd : 0 ≤ testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε := by
    have h := (testing_offset_bounds hL hμ hκ hε.le).1
    linarith
  have hp := testingObjective_success_subset hμ hR hκ (show |(1 : ℝ)| ≤ 1 by norm_num) hd hscale
  have hm := testingObjective_success_subset hμ hR hκ (show |(-1 : ℝ)| ≤ 1 by norm_num) hd hscale
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hp hx
  have hy' := hm hy
  change realCoord x ∈ successfulInterval (testingSlope L μ 1) _ ε at hx'
  change realCoord x ∈ successfulInterval (testingSlope L μ (-1)) _ ε at hy'
  rw [(testingSlope_signs L μ).1] at hx'
  rw [(testingSlope_signs L μ).2] at hy'
  exact Set.disjoint_left.mp (testing_intervals_disjoint
    (testing_slopes_ordered hL hμ).1 (testing_slopes_ordered hL hμ).2 hε) hx' hy'

end FreshGradientMinimax
