import FreshGradientMinimax.CappedPath
import FreshGradientMinimax.PenaltyObjective

/-! Actual globally admissible path instances, using the paper's a = L/4,
gamma = L/8, and beta = L/8192. The cap estimate 1000 beta is at most L/8,
so the admissibility holds throughout kappa >= 4, including the boundary.
The signal size M is unrestricted. No bounds on oracle query norms occur. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem cappedPathGradient_paper_lipschitz {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) {L δ R : ℝ}
    (hL : 0 < L) (hδ : 0 ≤ δ) (hR : 0 < R) (y y' : Euclid dy) :
    ‖cappedPathGradient V s (L / 8192) δ R y - cappedPathGradient V s (L / 8192) δ R y'‖ ≤
      L / 8 * ‖y - y'‖ := by
  have h := (cappedPathGradient_lipschitz V hs (by positivity : 0 < L / 8192) hδ hR).dist_le_mul y y'
  simp only [dist_eq_norm, NNReal.coe_mk] at h
  have hm := mul_nonneg hL.le (norm_nonneg (y - y'))
  nlinarith only [h, hm]

def pathObjective {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R) :
    NCObjective 1 dy L μ := by
  have hL : 0 < L := by linarith
  have hβ : 0 < L / 8192 := by positivity
  exact penaltyObjective (cappedPathEnergy V s (L / 8192) δ R)
    (cappedPathGradient V s (L / 8192) δ R) L μ d M
    (V (EuclideanSpace.single i 1)) (V (EuclideanSpace.single j 1)) hμ hκ
    (by simp) (cappedPathEnergy_convex V s hβ hδ hR)
    (cappedPathEnergy_hasFDerivAt V s hβ hδ hR)
    (cappedPathGradient_paper_lipschitz V hs hL hδ hR)

theorem pathObjective_initial_gradient {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R) :
    (pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).gradY 0 0 =
      M • V (EuclideanSpace.single j 1) := by
  have hβ : 0 ≤ L / 8192 := by
    have hL : 0 < L := by linarith
    positivity
  simp only [pathObjective, penaltyObjective, penaltySaddleGradY, realCoord_zero, mul_zero,
    zero_smul, smul_zero, sub_self, cappedPathGradient_zero V s hβ hδ hR.le, sub_zero, zero_add]

theorem pathObjective_initial_residual {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R) :
    ‖(pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).gradY 0 0‖ = |M| := by
  rw [pathObjective_initial_gradient, norm_smul]
  simp

theorem pathObjective_localized {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R)
    {G₀ : ℝ} (hM : |M| ≤ G₀) :
    (pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).DualLocalized G₀ := by
  simpa only [NCObjective.DualLocalized, pathObjective_initial_residual] using hM

theorem pathObjective_dualMax_of_core_root {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R)
    (x : Euclid 1) (y : Euclid dy) (hy : ‖y‖ ≤ R)
    (hroot : (L / 8 * realCoord x) • V (EuclideanSpace.single i 1) - μ • y -
      framedPathGradient V s (L / 8192) δ y + M • V (EuclideanSpace.single j 1) = 0) :
    (pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).dualMax x = y := by
  let F := pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR
  have hβ : 0 ≤ L / 8192 := by
    have hL : 0 < L := by linarith
    positivity
  have hg : F.gradY x y = 0 := by
    change (L / 8 * realCoord x) • V (EuclideanSpace.single i 1) - μ • y -
      cappedPathGradient V s (L / 8192) δ R y + M • V (EuclideanSpace.single j 1) = 0
    rw [cappedPathGradient_core V s hβ hδ hy]
    exact hroot
  apply Eq.symm
  apply F.dualMax_unique
  intro z
  have h := F.dual_strong x y z
  rw [hg, inner_zero_left, add_zero] at h
  have hn : 0 ≤ μ / 2 * ‖z - y‖ ^ 2 := by positivity
  linarith only [h, hn]

end FreshGradientMinimax
