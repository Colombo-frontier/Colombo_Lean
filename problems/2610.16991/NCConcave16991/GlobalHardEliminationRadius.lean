import NCConcave16991.GlobalHardConnectorDirection
import NCConcave16991.GlobalHardPaper
import NCConcave16991.BranchConstructionValue

/-! # The actual aggregate unconstrained multiplier and its public-ball radius -/

namespace NCConcave16991.GlobalHard
noncomputable section
open Set
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M m : ℕ} (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)] [∀ j k, FiniteDimensional ℝ (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))

def globalPaperOptimizer (z : Joint V) : Dual V := WithLp.toLp 2 (fun j ↦
  BranchConstruction.paperOptimizer (V j) (B j) (aProj V j z) (bProj V j z))

theorem globalPaperOptimizer_norm_sq_bound (z : Joint V) :
    ‖globalPaperOptimizer V B z‖ ^ 2 ≤
      (3 * ((m : ℝ) + 2) ^ 2 / BranchGeometry.beta ι) * ‖connectorTuple V z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, connectorTuple_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact BranchConstruction.paperOptimizer_norm_sq_bound (V j) (B j) (aProj V j z) (bProj V j z)

theorem globalPaperOptimizer_norm_bound (z : Joint V) :
    ‖globalPaperOptimizer V B z‖ ≤ Real.sqrt 3 * ((m : ℝ) + 2) *
      (Fintype.card ι : ℝ) ^ (1 / 4 : ℝ) * ‖connectorTuple V z‖ := by
  have hs : ‖globalPaperOptimizer V B z‖ ^ 2 ≤
      3 * ((m : ℝ) + 2) ^ 2 * Real.sqrt (Fintype.card ι) * ‖connectorTuple V z‖ ^ 2 := by
    simpa [BranchGeometry.beta, div_eq_mul_inv] using globalPaperOptimizer_norm_sq_bound V B z
  have hq : ((Fintype.card ι : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Fintype.card ι) := by
    rw [← BranchConstruction.sqrt_sqrt_card, Real.sq_sqrt (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hq]
  nlinarith only [hs]

/-- Connector control is sufficient for actual strict dual interiority. -/
theorem globalPaperOptimizer_mem_public_ball (z : Joint V)
    (hc : ‖connectorTuple V z‖ ≤ 43 / 4) :
    globalPaperOptimizer V B z ∈ Metric.ball 0 (publicDualRadius (Fintype.card ι) (m + 2)) := by
  let C : ℝ := Real.sqrt 3 * ((m : ℝ) + 2) * (Fintype.card ι : ℝ) ^ (1 / 4 : ℝ)
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound := (globalPaperOptimizer_norm_bound V B z).trans (mul_le_mul_of_nonneg_left hc hC.le)
  have hR : publicDualRadius (Fintype.card ι) (m + 2) = 20 * C := by
    simp only [publicDualRadius, C, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [Metric.mem_ball, dist_zero_right, hR]
  exact hbound.trans_lt (by nlinarith)

end
end NCConcave16991.GlobalHard
