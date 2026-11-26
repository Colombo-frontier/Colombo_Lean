import MatchingBounds1005.CUPGGuard
import MatchingBounds1005.CUPGLines
import MatchingBounds1005.CUPGProximal

/-! # Actual guarded phase geometry -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def guardNear (y previous : E) : E := y + (-(1 / 2) : ℝ) • (y - previous)
def guardFar (y previous : E) : E := y + (-3 : ℝ) • (y - previous)

theorem proximal_radius {f : E → ℝ} {α τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (start y : E) (hprox : regularized f α start y ≤ f start)
    (hfloor : f start - α * τ ^ 2 ≤ f y) : ‖y - start‖ ≤ τ := by
  unfold regularized at hprox
  have hs : ‖y - start‖ ^ 2 ≤ τ ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) hτ).mp hs

theorem extrapolation_radius {τ θ : ℝ} (hτ : 0 ≤ τ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (start y previous : E) (hy : ‖y - start‖ ≤ τ) (hp : ‖previous - start‖ ≤ τ) :
    ‖y + θ • (y - previous) - start‖ ≤ 3 * τ := by
  have hdiff : ‖y - previous‖ ≤ 2 * τ := by
    have he : y - previous = (y - start) - (previous - start) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have he : y + θ • (y - previous) - start = (y - start) + θ • (y - previous) := by abel
  rw [he]
  calc
    _ ≤ ‖y - start‖ + ‖θ • (y - previous)‖ := norm_add_le _ _
    _ = ‖y - start‖ + θ * ‖y - previous‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    _ ≤ 3 * τ := by nlinarith [norm_nonneg (y - previous)]

theorem extrapolation_value {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {L α τ θ : ℝ} (hL : 0 ≤ L) (hα : 0 < α) (hτ : 0 ≤ τ)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hscale : 16 * L * τ ^ 2 ≤ α)
    (hdir : DirectionalLip f 3 L) (start y previous : E)
    (hy : f y ≤ f start) (hp : f previous ≤ f start)
    (hnear : f start - α * τ ^ 2 ≤ f (guardNear y previous))
    (hfar : f start - α * τ ^ 2 ≤ f (guardFar y previous))
    (hyRadius : ‖y - start‖ ≤ τ) (hpRadius : ‖previous - start‖ ≤ τ) :
    f (y + θ • (y - previous)) ≤ f start + 14 * α * τ ^ 2 := by
  let d := y - previous
  let h : ℝ → ℝ := fun t => -f start + line f y d t
  have hthird (s t : ℝ) : |iteratedDeriv 3 h s - iteratedDeriv 3 h t| ≤
      (L * ‖d‖ ^ 4) * |s - t| := by
    simp only [h, iteratedDeriv_const_add (by decide : 0 < 3)]
    exact directional_lip_scaled hf hdir y d t s
  have hzero : h 0 ≤ 0 := by simpa [h, line] using sub_nonpos.mpr hy
  have hone : h (-1) ≤ 0 := by
    have he : y + (-1 : ℝ) • d = previous := by dsimp [d]; module
    change -f start + f (y + (-1 : ℝ) • d) ≤ 0
    rw [he]
    linarith
  have hhalf : -(α * τ ^ 2) ≤ h (-(1 / 2)) := by
    change -(α * τ ^ 2) ≤ -f start + f (guardNear y previous)
    linarith
  have hthree : -(α * τ ^ 2) ≤ h (-3) := by
    change -(α * τ ^ 2) ≤ -f start + f (guardFar y previous)
    linarith
  have hdiff : ‖d‖ ≤ 2 * τ := by
    have he : d = (y - start) - (previous - start) := by dsimp [d]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hfour : ‖d‖ ^ 4 ≤ (2 * τ) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hdiff 4
  have hnoise : L * ‖d‖ ^ 4 ≤ α * τ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hfour hL
    have hs := mul_le_mul_of_nonneg_right hscale (sq_nonneg τ)
    nlinarith only [hm, hs]
  have hg := guarded_extrapolation (contDiff_const.add (line_smooth hf y d))
    (by positivity : 0 ≤ L * ‖d‖ ^ 4) (by positivity : 0 ≤ α * τ ^ 2)
    hthird hzero hone hhalf hthree hθ hθone
  dsimp only [h, line] at hg
  simp only [zero_smul, add_zero] at hg
  nlinarith only [hg, hnoise, hy]

theorem momentum_bounds {q : ℝ} (hq : 0 ≤ q) (hqone : q ≤ 1) :
    0 ≤ (1 - q) / (1 + q) ∧ (1 - q) / (1 + q) ≤ 1 := by
  have hn : 0 < 1 + q := by linarith
  exact ⟨div_nonneg (sub_nonneg.mpr hqone) hn.le, (div_le_one hn).mpr (by linarith)⟩

end MatchingBounds1005.CUPG
