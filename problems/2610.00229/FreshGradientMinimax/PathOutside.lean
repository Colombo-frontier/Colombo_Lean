import FreshGradientMinimax.PathHorizon

/-! Exact response equality outside the cap, for the actual binary family.
This handles arbitrary large queries without modifying or clipping them. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem pathHardObjective_gradX_equal {n dy : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ) (s t L μ ε : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (x : Euclid 1) (y : Euclid dy) :
    (pathHardObjective V k s L μ ε hμ hκ hε hs).gradX x y =
      (pathHardObjective V k t L μ ε hμ hκ hε ht).gradX x y := rfl

theorem pathHardObjective_gradY_outside {n dy : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ) (s L μ ε : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1)
    (x : Euclid 1) (y : Euclid dy) (hy : 2 * pathHardRadius L μ ε n ≤ ‖y‖) :
    (pathHardObjective V k s L μ ε hμ hκ hε hs).gradY x y =
      (L / 8 * realCoord x) • V (EuclideanSpace.single 0 1) - μ • y - (8 * (L / 8192)) • y +
        pathHardSignal L μ ε n • V (EuclideanSpace.single (Fin.last n) 1) := by
  have hL : 0 < L := by linarith
  change (L / 8 * realCoord x) • V (EuclideanSpace.single 0 1) - μ • y -
    cappedPathGradient V (pathSignsFromVertices (tailVertexSigns k s)) (L / 8192)
      (pathHardFlatWidth L μ ε n) (pathHardRadius L μ ε n) y +
        pathHardSignal L μ ε n • V (EuclideanSpace.single (Fin.last n) 1) = _
  rw [cappedPathGradient_outside V (pathSignsFromVertices_abs (tailVertexSigns_sq k hs))
    (by positivity) (pathHardFlatWidth_pos hL hμ hε n).le (pathHardRadius_pos hL hμ hε n) hy]

theorem pathHardObjective_jointGradient_outside {n dy : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ) (s t L μ ε : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (z : Joint 1 dy) (hz : 2 * pathHardRadius L μ ε n ≤ ‖z.2‖) :
    (pathHardObjective V k s L μ ε hμ hκ hε hs).jointGradient z =
      (pathHardObjective V k t L μ ε hμ hκ hε ht).jointGradient z := by
  apply Prod.ext
  · exact pathHardObjective_gradX_equal V k s t L μ ε hμ hκ hε hs ht z.1 z.2
  · exact (pathHardObjective_gradY_outside V k s L μ ε hμ hκ hε hs z.1 z.2 hz).trans
      (pathHardObjective_gradY_outside V k t L μ ε hμ hκ hε ht z.1 z.2 hz).symm

theorem pathHardObjective_exactOracle_outside {n dy : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ) (s t L μ ε σ : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (z : Joint 1 dy) (hz : 2 * pathHardRadius L μ ε n ≤ ‖z.2‖) :
    (FreshOracle.exact (pathHardObjective V k s L μ ε hμ hκ hε hs) σ).kernel z =
      (FreshOracle.exact (pathHardObjective V k t L μ ε hμ hκ hε ht) σ).kernel z := by
  rw [FreshOracle.exact_kernel, FreshOracle.exact_kernel,
    pathHardObjective_jointGradient_outside V k s t L μ ε hμ hκ hε hs ht z hz]

end FreshGradientMinimax
