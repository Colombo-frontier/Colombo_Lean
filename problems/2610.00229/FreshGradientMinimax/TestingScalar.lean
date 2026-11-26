import FreshGradientMinimax.ClipTaylor
import FreshGradientMinimax.Testing

/-! Global analytic estimates for the concrete two-dimensional testing family. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def testingFunction (a b μ d R s x y : ℝ) : ℝ :=
  a / 2 * x ^ 2 + d * x + b * x * y - 3 * μ * y ^ 2 + s * μ * clipSquare R y
def testingGradX (a b d x y : ℝ) : ℝ := a * x + d + b * y
def testingGradY (b μ R s x y : ℝ) : ℝ := b * x - 6 * μ * y + s * μ * clipSquareSlope R y

theorem testingGradY_lipschitz {μ R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hs : |s| ≤ 1) (b x y z : ℝ) :
    |testingGradY b μ R s x y - testingGradY b μ R s x z| ≤
      (37 * μ / 4) * |y - z| := by
  have hm : |s * μ| ≤ μ := by
    rw [abs_mul, abs_of_pos hμ]
    nlinarith
  have hc := mul_le_mul hm (clipSquareSlope_lipschitz hR y z)
    (abs_nonneg _) hμ.le
  have he : testingGradY b μ R s x y - testingGradY b μ R s x z =
      -(6 * μ * (y - z)) + s * μ * (clipSquareSlope R y - clipSquareSlope R z) := by
    unfold testingGradY; ring
  rw [he]
  have ht := abs_add (-(6 * μ * (y - z)))
    (s * μ * (clipSquareSlope R y - clipSquareSlope R z))
  rw [abs_neg, abs_mul (6 * μ), abs_of_pos (by positivity : 0 < 6 * μ), abs_mul (s * μ)] at ht
  nlinarith only [ht, hc]

theorem testingFunction_strongConcave {μ R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hs : |s| ≤ 1) (a b d x y z : ℝ) :
    testingFunction a b μ d R s x z ≤ testingFunction a b μ d R s x y +
      testingGradY b μ R s x y * (z - y) - μ / 2 * (z - y) ^ 2 := by
  have hm : |s * μ| ≤ μ := by rw [abs_mul, abs_of_pos hμ]; nlinarith
  have hc := mul_le_mul hm (clipSquare_taylor hR y z) (abs_nonneg _) hμ.le
  rw [← abs_mul] at hc
  have hu := (le_abs_self (s * μ *
    (clipSquare R z - clipSquare R y - clipSquareSlope R y * (z - y)))).trans hc
  unfold testingFunction testingGradY
  nlinarith only [hu, mul_nonneg hμ.le (sq_nonneg (z - y))]

theorem testingFunction_jointSmooth {L μ R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hs : |s| ≤ 1) (d x y x' y' : ℝ) :
    (testingGradX (L / 16) (L / 16) d x y - testingGradX (L / 16) (L / 16) d x' y') ^ 2 +
      (testingGradY (L / 16) μ R s x y - testingGradY (L / 16) μ R s x' y') ^ 2 ≤
        L ^ 2 * ((x - x') ^ 2 + (y - y') ^ 2) := by
  have hL : 0 < L := by linarith
  have ha : 0 ≤ L / 16 := by positivity
  have hc : 37 * μ / 4 ≤ L / 16 := by linarith
  have hdx := abs_nonneg (x - x')
  have hdy := abs_nonneg (y - y')
  have hgx : |testingGradX (L / 16) (L / 16) d x y -
      testingGradX (L / 16) (L / 16) d x' y'| ≤ L / 16 * (|x - x'| + |y - y'|) := by
    have he : testingGradX (L / 16) (L / 16) d x y -
        testingGradX (L / 16) (L / 16) d x' y' = L / 16 * ((x - x') + (y - y')) := by
      unfold testingGradX; ring
    rw [he, abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (abs_add _ _) ha
  have hgy : |testingGradY (L / 16) μ R s x y - testingGradY (L / 16) μ R s x' y'| ≤
      L / 16 * (|x - x'| + |y - y'|) := by
    have he : testingGradY (L / 16) μ R s x y - testingGradY (L / 16) μ R s x' y' =
        L / 16 * (x - x') + (testingGradY (L / 16) μ R s x' y - testingGradY (L / 16) μ R s x' y') := by
      unfold testingGradY; ring
    rw [he]
    have ht := abs_add (L / 16 * (x - x'))
      (testingGradY (L / 16) μ R s x' y - testingGradY (L / 16) μ R s x' y')
    rw [abs_mul, abs_of_nonneg ha] at ht
    have hl := testingGradY_lipschitz hμ hR hs (L / 16) x' y y'
    have hm := mul_le_mul_of_nonneg_right hc hdy
    linarith
  have hb : 0 ≤ L / 16 * (|x - x'| + |y - y'|) := by positivity
  have hx2 := (sq_le_sq₀ (abs_nonneg _) hb).mpr hgx
  have hy2 := (sq_le_sq₀ (abs_nonneg _) hb).mpr hgy
  rw [sq_abs] at hx2 hy2
  have hsum : (|x - x'| + |y - y'|) ^ 2 ≤ 2 * ((x - x') ^ 2 + (y - y') ^ 2) := by
    nlinarith only [sq_nonneg (|x - x'| - |y - y'|), sq_abs (x - x'), sq_abs (y - y')]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (L / 16))
  have hz : 0 ≤ L ^ 2 * ((x - x') ^ 2 + (y - y') ^ 2) := by positivity
  nlinarith only [hx2, hy2, hh, hz]

end FreshGradientMinimax
