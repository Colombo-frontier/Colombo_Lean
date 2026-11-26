import FreshGradientMinimax.RobinEndpointMap

/-! Original multi-chain edge matrices on one finite Euclidean primal and
dual space. k is T−1; the subchain length is n+2. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def robinDualMap (n k : ℕ) : Euclid (k * (n + 2)) →L[ℝ] Euclid (k * (n + 3)) :=
  euclidBlockMap k (robinIncidence (n + 2))

def robinPrimalMap (n k : ℕ) : Euclid (k * 2 + 1) →L[ℝ] Euclid (k * (n + 3)) :=
  (euclidBlockMap k (robinEndpointMap n)).comp (euclidDropLast (k * 2))

def robinBlockEdges (n k : ℕ) (q : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * (n + 3)) :=
  robinDualMap n k y + robinPrimalMap n k q

theorem robinDualMap_block {n k : ℕ} (y : Euclid (k * (n + 2))) (i : Fin k) :
    euclidBlock i (robinDualMap n k y) = robinIncidence (n + 2) (euclidBlock i y) := euclidBlockMap_block _ _ _

theorem robinPrimalMap_block {n k : ℕ} (q : Euclid (k * 2 + 1)) (i : Fin k) :
    euclidBlock i (robinPrimalMap n k q) = robinEdgeShift n (q (interleavedX i)) (q (interleavedZ i) / 2) := by
  rw [robinPrimalMap, ContinuousLinearMap.comp_apply, euclidBlockMap_block, robinEndpointMap_apply]
  simp only [euclidBlock_apply, euclidDropLast_apply, interleavedX, interleavedZ]

theorem robinBlockEdges_block {n k : ℕ} (q : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) (i : Fin k) :
    euclidBlock i (robinBlockEdges n k q y) =
      robinIncidence (n + 2) (euclidBlock i y) + robinEdgeShift n (q (interleavedX i)) (q (interleavedZ i) / 2) := by
  rw [robinBlockEdges, map_add, robinDualMap_block, robinPrimalMap_block]

theorem robinDualMap_norm (n k : ℕ) (y : Euclid (k * (n + 2))) :
    ‖robinDualMap n k y‖ ≤ 2 * ‖y‖ :=
  euclidBlockMap_norm _ (by norm_num) (robinIncidence_norm (by omega)) y

theorem robinDualMap_opNorm (n k : ℕ) : ‖robinDualMap n k‖ ≤ 2 :=
  (euclidBlockMap_opNorm k _).trans (robinIncidence_opNorm (by omega))

theorem robinPrimalMap_norm {n : ℕ} (hn : 10 ≤ n + 2) (k : ℕ) (q : Euclid (k * 2 + 1)) :
    ‖robinPrimalMap n k q‖ ≤ Real.sqrt (robinC (n + 2)) * ‖q‖ :=
  (euclidBlockMap_norm _ (Real.sqrt_nonneg _) (robinEndpointMap_norm hn) _).trans
    (mul_le_mul_of_nonneg_left (euclidDropLast_norm q) (Real.sqrt_nonneg _))

theorem robinPrimalMap_opNorm {n : ℕ} (hn : 10 ≤ n + 2) (k : ℕ) :
    ‖robinPrimalMap n k‖ ≤ Real.sqrt (robinC (n + 2)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (robinPrimalMap_norm hn k)

theorem robinPrimalMap_opNorm_bound {n : ℕ} (hn : 10 ≤ n + 2) (k : ℕ) :
    ‖robinPrimalMap n k‖ ≤ 28 / 3 := (robinPrimalMap_opNorm hn k).trans (robin_sqrt_C_bound hn)

theorem robinPrimalMap_opNorm_sq {n : ℕ} (hn : 10 ≤ n + 2) (k : ℕ) :
    ‖robinPrimalMap n k‖ ^ 2 ≤ 84 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (robinPrimalMap_opNorm hn k) 2
  rw [Real.sq_sqrt (le_trans (by norm_num) (robin_coefficients_bounds hn).1)] at h
  exact h.trans (robin_coefficients_bounds hn).2.1

theorem robinPrimalMap_adjoint (n k : ℕ) :
    (robinPrimalMap n k)† = (pathPadLeft (k * 2)).comp (euclidBlockMap k ((robinEndpointMap n)†)) := by
  rw [robinPrimalMap, ContinuousLinearMap.adjoint_comp, euclidDropLast_adjoint, euclidBlockMap_adjoint]

theorem robinPrimalMap_adjoint_bounded_norm {n k : ℕ} (hn : 10 ≤ n + 2) {B : ℝ}
    (hB : 0 ≤ B) (w : Euclid (k * (n + 3))) (hw : ∀ e, |w e| ≤ B) :
    ‖((robinPrimalMap n k)†) w‖ ≤ 11 * B * Real.sqrt k := by
  rw [robinPrimalMap_adjoint, ContinuousLinearMap.comp_apply, pathPadLeft_norm]
  change ‖euclidJoin (fun i : Fin k => ((robinEndpointMap n)†) (euclidBlock i w))‖ ≤ _
  apply euclidJoin_norm_bound (by positivity)
  intro i
  exact robinEndpointMap_adjoint_bounded_norm hn hB _ (fun e => hw (finProdFinEquiv (i, e)))

theorem robinPrimalMap_adjoint_coordinate {n k : ℕ} (hn : 10 ≤ n + 2) {B : ℝ}
    (hB : 0 ≤ B) (w : Euclid (k * (n + 3))) (hw : ∀ e, |w e| ≤ B) (j : Fin (k * 2 + 1)) :
    |((robinPrimalMap n k)†) w j| ≤ (28 / 3) * B := by
  rw [robinPrimalMap_adjoint, ContinuousLinearMap.comp_apply, pathPadLeft_apply]
  refine Fin.lastCases ?_ (fun a => ?_) j
  · rw [Fin.snoc_last, abs_zero]
    positivity
  · rw [Fin.snoc_castSucc]
    change |((robinEndpointMap n)†) (euclidBlock (finProdFinEquiv.symm a).1 w) (finProdFinEquiv.symm a).2| ≤ _
    apply robinEndpointMap_adjoint_coordinate hn hB
    intro e
    exact hw (finProdFinEquiv ((finProdFinEquiv.symm a).1, e))

end FreshGradientMinimax
