import FreshGradientMinimax.ConvexGradient

/-! Bilinear coupling of a scalar quadratic to a convex dual penalty.
The estimates use the Euclidean sum of component squares. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def penaltySaddleFunction (Q : E → ℝ) (a γ μ d M : ℝ) (u v : E) (x : ℝ) (y : E) : ℝ :=
  a / 2 * x ^ 2 + d * x + γ * x * ⟪u, y⟫_ℝ - μ / 2 * ‖y‖ ^ 2 - Q y + M * ⟪v, y⟫_ℝ

def penaltySaddleGradX (a γ d : ℝ) (u : E) (x : ℝ) (y : E) : ℝ :=
  a * x + d + γ * ⟪u, y⟫_ℝ

def penaltySaddleGradY (G : E → E) (γ μ M : ℝ) (u v : E) (x : ℝ) (y : E) : E :=
  (γ * x) • u - μ • y - G y + M • v

theorem penaltySaddle_strongConcave {Q : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ Set.univ Q) (hd : ∀ y, HasFDerivAt Q (innerSL ℝ (G y)) y)
    (a γ μ d M : ℝ) (u v : E) (x : ℝ) :
    StrongConcaveGradient (penaltySaddleFunction Q a γ μ d M u v x)
      (penaltySaddleGradY G γ μ M u v x) μ := by
  have h := convex_penalty_strongConcave hc hd μ (a / 2 * x ^ 2 + d * x)
    ((γ * x) • u + M • v)
  intro y z
  have ht := h y z
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at ht
  simp only [penaltySaddleFunction, penaltySaddleGradY, inner_add_left, inner_sub_left,
    real_inner_smul_left]
  linarith only [ht]

theorem penaltySaddleGradX_difference {a γ : ℝ} (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (d : ℝ) (u : E) (hu : ‖u‖ ≤ 1) (x x' : ℝ) (y y' : E) :
    |penaltySaddleGradX a γ d u x y - penaltySaddleGradX a γ d u x' y'| ≤
      a * |x - x'| + γ * ‖y - y'‖ := by
  have hi : |⟪u, y - y'⟫_ℝ| ≤ ‖y - y'‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)
  have he : penaltySaddleGradX a γ d u x y - penaltySaddleGradX a γ d u x' y' =
      a * (x - x') + γ * ⟪u, y - y'⟫_ℝ := by
    simp only [penaltySaddleGradX, inner_sub_right]; ring
  rw [he]
  have ht := abs_add (a * (x - x')) (γ * ⟪u, y - y'⟫_ℝ)
  rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hγ] at ht
  exact ht.trans (add_le_add_left (mul_le_mul_of_nonneg_left hi hγ) _)

theorem penaltySaddleGradY_difference {G : E → E} {γ μ K : ℝ}
    (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hG : ∀ y y', ‖G y - G y'‖ ≤ K * ‖y - y'‖)
    (M : ℝ) (u v : E) (hu : ‖u‖ ≤ 1) (x x' : ℝ) (y y' : E) :
    ‖penaltySaddleGradY G γ μ M u v x y - penaltySaddleGradY G γ μ M u v x' y'‖ ≤
      γ * |x - x'| + (μ + K) * ‖y - y'‖ := by
  have he : penaltySaddleGradY G γ μ M u v x y - penaltySaddleGradY G γ μ M u v x' y' =
      (γ * (x - x')) • u - μ • (y - y') - (G y - G y') := by
    dsimp [penaltySaddleGradY]; module
  rw [he]
  have h₁ := norm_sub_le ((γ * (x - x')) • u - μ • (y - y')) (G y - G y')
  have h₂ := norm_sub_le ((γ * (x - x')) • u) (μ • (y - y'))
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hγ, abs_of_nonneg hμ] at h₂
  have h₃ := mul_le_of_le_one_right (show 0 ≤ γ * |x - x'| by positivity) hu
  have h₄ := hG y y'
  nlinarith only [h₁, h₂, h₃, h₄]

theorem penaltySaddle_jointSmooth {G : E → E} {L μ : ℝ}
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L)
    (hG : ∀ y y', ‖G y - G y'‖ ≤ L / 8 * ‖y - y'‖)
    (d M : ℝ) (u v : E) (hu : ‖u‖ ≤ 1) (x x' : ℝ) (y y' : E) :
    (penaltySaddleGradX (L / 4) (L / 8) d u x y -
      penaltySaddleGradX (L / 4) (L / 8) d u x' y') ^ 2 +
    ‖penaltySaddleGradY G (L / 8) μ M u v x y -
      penaltySaddleGradY G (L / 8) μ M u v x' y'‖ ^ 2 ≤
        L ^ 2 * ((x - x') ^ 2 + ‖y - y'‖ ^ 2) := by
  have hL : 0 < L := by linarith
  have hx := penaltySaddleGradX_difference (show 0 ≤ L / 4 by positivity)
    (show 0 ≤ L / 8 by positivity) d u hu x x' y y'
  have hy := penaltySaddleGradY_difference (show 0 ≤ L / 8 by positivity) hμ.le hG M u v hu x x' y y'
  have hB : 0 ≤ 3 * L / 8 * (|x - x'| + ‖y - y'‖) := by positivity
  have hxB : |penaltySaddleGradX (L / 4) (L / 8) d u x y -
      penaltySaddleGradX (L / 4) (L / 8) d u x' y'| ≤
        3 * L / 8 * (|x - x'| + ‖y - y'‖) := by
    nlinarith [mul_nonneg hL.le (abs_nonneg (x - x')), mul_nonneg hL.le (norm_nonneg (y - y'))]
  have hyB : ‖penaltySaddleGradY G (L / 8) μ M u v x y -
      penaltySaddleGradY G (L / 8) μ M u v x' y'‖ ≤
        3 * L / 8 * (|x - x'| + ‖y - y'‖) := by
    have hc := mul_le_mul_of_nonneg_right hκ (norm_nonneg (y - y'))
    nlinarith [mul_nonneg hL.le (abs_nonneg (x - x'))]
  have hx2 := (sq_le_sq₀ (abs_nonneg _) hB).mpr hxB
  have hy2 := (sq_le_sq₀ (norm_nonneg _) hB).mpr hyB
  rw [sq_abs] at hx2
  have hsum : (|x - x'| + ‖y - y'‖) ^ 2 ≤ 2 * ((x - x') ^ 2 + ‖y - y'‖ ^ 2) := by
    nlinarith only [sq_nonneg (|x - x'| - ‖y - y'‖), sq_abs (x - x')]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (3 * L / 8))
  have hz : 0 ≤ L ^ 2 * ((x - x') ^ 2 + ‖y - y'‖ ^ 2) := by positivity
  nlinarith only [hx2, hy2, hh, hz]

end FreshGradientMinimax
