import FreshGradientMinimax.PathValue
import FreshGradientMinimax.ScalarDecision
import FreshGradientMinimax.Minimax

/-! Successful outputs of the actual signed path lie in the paper's two
disjoint intervals, independently of the ambient frame. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem pathHardObjective_success_interval {n dy k : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (hk0 : 0 < k) (hkn : k ≤ n)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1)
    (hL : 0 < L) {x : Euclid 1}
    (hx : x ∈ (pathHardObjective V k s L μ ε hμ hκ hε hs).successSet ε) :
    realCoord x ∈ pathDecisionInterval s ε (pathHardSlope L μ hL hμ n) := by
  let F := pathHardObjective V k s L μ ε hμ hκ hε hs
  have habs : |s| ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have hnorm : ‖F.primalGradient x‖ ≤ ε := by
    change ‖gradient F.value x‖ ≤ ε at hx
    rwa [F.true_primal_gradient] at hx
  have hscalar : |realCoord (F.primalGradient (realVector (realCoord x)))| ≤ ε := by
    rwa [realVector_coord, realCoord_norm]
  apply scalar_success_interval (pathHardObjective_primal_monotone V k s L μ ε hμ hκ hε hs)
    habs hε (pathHardSlope_pos hL hμ n) _ hscalar
  intro t ht
  simpa only [realCoord_vector] using pathHardObjective_primalApproximation V hk0 hkn s L μ ε
    hμ hκ hε hs hL (realVector t) (by simpa only [realCoord_vector] using ht)

theorem pathHardObjective_success_disjoint {n dy dz k : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (W : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dz)
    (hk0 : 0 < k) (hkn : k ≤ n) (L μ ε : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) :
    Disjoint ((pathHardObjective V k 1 L μ ε hμ hκ hε (by norm_num)).successSet ε)
      ((pathHardObjective W k (-1) L μ ε hμ hκ hε (by norm_num)).successSet ε) := by
  have hL : 0 < L := by linarith
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hp := pathHardObjective_success_interval V hk0 hkn 1 L μ ε hμ hκ hε (by norm_num) hL hx
  have hm := pathHardObjective_success_interval W hk0 hkn (-1) L μ ε hμ hκ hε (by norm_num) hL hy
  exact Set.disjoint_left.mp (pathDecisionInterval_disjoint hε (pathHardSlope_pos hL hμ n)) hp hm

end FreshGradientMinimax
