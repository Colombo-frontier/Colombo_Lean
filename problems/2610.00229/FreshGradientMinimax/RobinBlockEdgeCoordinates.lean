import FreshGradientMinimax.RobinBlockMaps
import FreshGradientMinimax.RobinEnergyFormula

/-! Literal rows of the actual block edge vector, in global coordinates. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robinBlockEdges_first {n k : ℕ} (q : Euclid (k * 2 + 1))
    (y : Euclid (k * (n + 2))) (i : Fin k) :
    robinBlockEdges n k q y (finProdFinEquiv (i, (0 : Fin (n + 3)))) =
      -(Real.sqrt (robinC (n + 2))) * q (interleavedX i) +
        (Real.sqrt (n + 2 : ℕ))⁻¹ * y (finProdFinEquiv (i, (0 : Fin (n + 2)))) := by
  change euclidBlock i (robinBlockEdges n k q y) 0 = _
  rw [robinBlockEdges_block, robinEdgeVector_first, euclidBlock_apply]
  ring

theorem robinBlockEdges_last {n k : ℕ} (q : Euclid (k * 2 + 1))
    (y : Euclid (k * (n + 2))) (i : Fin k) :
    robinBlockEdges n k q y (finProdFinEquiv (i, Fin.last (n + 2))) =
      -((Real.sqrt (n + 2 : ℕ))⁻¹) * y (finProdFinEquiv (i, Fin.last (n + 1))) +
        -(Real.sqrt (robinC (n + 2)) / 2) * q (interleavedZ i) := by
  change euclidBlock i (robinBlockEdges n k q y) (Fin.last (n + 2)) = _
  rw [robinBlockEdges_block, robinEdgeVector_last, euclidBlock_apply]
  ring

theorem robinBlockEdges_interior {n k : ℕ} (q : Euclid (k * 2 + 1))
    (y : Euclid (k * (n + 2))) (i : Fin k) (a : Fin (n + 1)) :
    robinBlockEdges n k q y (finProdFinEquiv (i, a.succ.castSucc)) =
      (-1) * y (finProdFinEquiv (i, a.castSucc)) + 1 * y (finProdFinEquiv (i, a.succ)) := by
  change euclidBlock i (robinBlockEdges n k q y) a.succ.castSucc = _
  rw [robinBlockEdges_block, robinEdgeVector_interior, euclidBlock_apply, euclidBlock_apply]
  ring

end FreshGradientMinimax
