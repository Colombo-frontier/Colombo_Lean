import FreshGradientMinimax.TestingRegions
import FreshGradientMinimax.TestingGap

/-! The parameterized, globally admissible binary family in Appendix D,
with a uniform bound on the difference of its original oracle means. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def testingRadius (L μ ε : ℝ) : ℝ :=
  2 * (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε + ε) / (L / 16)

theorem testingRadius_pos {L μ ε : ℝ} (hμ : 0 < μ) (hκ : 1120 * μ ≤ L) (hε : 0 < ε) :
    0 < testingRadius L μ ε := by
  have hL : 0 < L := by linarith
  have hd := (testing_offset_bounds hL hμ hκ hε.le).1
  unfold testingRadius
  exact div_pos (by linarith) (by positivity)

theorem testingRadius_scale {L μ ε : ℝ} (hμ : 0 < μ) (hκ : 1120 * μ ≤ L) (hε : 0 < ε) :
    testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε + ε ≤
      (L / 16) * testingRadius L μ ε := by
  have hL : 0 < L := by linarith
  have hd := (testing_offset_bounds hL hμ hκ hε.le).1
  have he : (L / 16) * testingRadius L μ ε =
      2 * (testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε + ε) := by
    unfold testingRadius
    field_simp
    ring
  rw [he]
  linarith

theorem testingRadius_bound {L μ ε : ℝ} (hμ : 0 < μ) (hκ : 1120 * μ ≤ L) (hε : 0 < ε) :
    testingRadius L μ ε ≤ 448 * ε / L := by
  have hL : 0 < L := by linarith
  have hd := (testing_offset_bounds hL hμ hκ hε.le).2
  unfold testingRadius
  apply (div_le_iff₀ (show 0 < L / 16 by positivity)).mpr
  have he : 448 * ε / L * (L / 16) = 28 * ε := by field_simp; ring
  rw [he]
  linarith

def testingHardObjective (p : Parameters) (hκ : 1120 * p.μ ≤ p.L) (s : ℝ) (hs : |s| ≤ 1) :
    NCObjective 1 1 p.L p.μ :=
  testingObjective p.L p.μ (testingOffset (testingSlopePlus p.L p.μ) (testingSlopeMinus p.L p.μ) p.ε)
    (testingRadius p.L p.μ p.ε) s p.μ_pos (testingRadius_pos p.μ_pos hκ p.ε_pos) hκ hs

theorem testingHardObjective_inClass (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hgap : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap) (s : ℝ) (hs : |s| ≤ 1) :
    InLocalizedClass (testingHardObjective p hκ s hs) p.gap (some p.G) := by
  refine ⟨?_, testingObjective_localized p.μ_pos _ hκ hs p.G_nonneg⟩
  intro x
  exact (testingObjective_gap_rate p.μ_pos (testingRadius_pos p.μ_pos hκ p.ε_pos)
    hκ p.ε_pos.le hs x).trans hgap

theorem testingHardObjective_success_disjoint (p : Parameters) (hκ : 1120 * p.μ ≤ p.L) :
    Disjoint ((testingHardObjective p hκ 1 (by norm_num)).successSet p.ε)
      ((testingHardObjective p hκ (-1) (by norm_num)).successSet p.ε) :=
  testingObjective_success_disjoint p.μ_pos (testingRadius_pos p.μ_pos hκ p.ε_pos)
    hκ p.ε_pos (testingRadius_scale p.μ_pos hκ p.ε_pos)

theorem testingHardObjective_gradX_equal (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (x y : Euclid 1) :
    (testingHardObjective p hκ 1 (by norm_num)).gradX x y =
      (testingHardObjective p hκ (-1) (by norm_num)).gradX x y := rfl

theorem testingHardObjective_gradY_difference (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (x y : Euclid 1) :
    ‖(testingHardObjective p hκ 1 (by norm_num)).gradY x y -
      (testingHardObjective p hκ (-1) (by norm_num)).gradY x y‖ ≤ 1344 * p.μ * p.ε / p.L := by
  have hμ := p.μ_pos
  change ‖realVector (testingGradY (p.L / 16) p.μ (testingRadius p.L p.μ p.ε) 1 (realCoord x) (realCoord y)) -
    realVector (testingGradY (p.L / 16) p.μ (testingRadius p.L p.μ p.ε) (-1) (realCoord x) (realCoord y))‖ ≤ _
  rw [realVector_sub, realVector_norm]
  have he : testingGradY (p.L / 16) p.μ (testingRadius p.L p.μ p.ε) 1 (realCoord x) (realCoord y) -
      testingGradY (p.L / 16) p.μ (testingRadius p.L p.μ p.ε) (-1) (realCoord x) (realCoord y) =
        2 * p.μ * clipSquareSlope (testingRadius p.L p.μ p.ε) (realCoord y) := by
    unfold testingGradY; ring
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2 * p.μ)]
  have hc := mul_le_mul_of_nonneg_left
    (clipSquareSlope_bound (testingRadius_pos p.μ_pos hκ p.ε_pos) (realCoord y))
    (show 0 ≤ 2 * p.μ by positivity)
  have hr := mul_le_mul_of_nonneg_left (testingRadius_bound p.μ_pos hκ p.ε_pos)
    (show 0 ≤ 3 * p.μ by positivity)
  calc
    _ ≤ 3 * p.μ * testingRadius p.L p.μ p.ε := by linarith only [hc]
    _ ≤ 3 * p.μ * (448 * p.ε / p.L) := hr
    _ = 1344 * p.μ * p.ε / p.L := by ring

theorem testingHardObjective_mean_separation (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (x y : Euclid 1) :
    ‖(testingHardObjective p hκ 1 (by norm_num)).gradY x y -
      (testingHardObjective p hκ (-1) (by norm_num)).gradY x y‖ ^ 2 ≤
        1806336 * p.μ ^ 2 * p.ε ^ 2 / p.L ^ 2 := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hμ := p.μ_pos
  have hε := p.ε_pos
  have h := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 1344 * p.μ * p.ε / p.L by positivity)).mpr
    (testingHardObjective_gradY_difference p hκ x y)
  convert h using 1
  ring

end FreshGradientMinimax
