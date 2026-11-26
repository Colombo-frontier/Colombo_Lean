import NCConcave16991.GlobalHardEliminationRadius
import NCConcave16991.GlobalHardStateRestriction
import NCConcave16991.GlobalHardDual

/-! # Actual global dual elimination, attainment, and uniqueness -/

namespace NCConcave16991.GlobalHard
noncomputable section
open Set
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M m : ℕ} (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)] [∀ j k, FiniteDimensional ℝ (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

def eliminatedValue (z : Joint V) : ℝ := ∑ j,
  (BranchConstruction.portValue (V j) (B j) (aProj V j z) (bProj V j z) + outerAt V u v z j)

theorem average_at_globalPaperOptimizer (z : Joint V) :
    average V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (atDual V (WithLp.fst z) (globalPaperOptimizer V B z)) =
      eliminatedValue V B u v z := by
  rw [average_eq_sum]
  unfold eliminatedValue
  apply Finset.sum_congr rfl
  intro j _
  change BranchConstruction.paperAverage (V j) (B j) (aProj V j z) (bProj V j z)
      (BranchConstruction.paperOptimizer (V j) (B j) (aProj V j z) (bProj V j z)) + outerAt V u v z j = _
  rw [BranchConstruction.paperAverage_at_optimizer]

theorem average_le_eliminatedValue (z : Joint V) (w : Dual V) :
    average V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (atDual V (WithLp.fst z) w) ≤ eliminatedValue V B u v z := by
  rw [average_eq_sum]
  unfold eliminatedValue
  apply Finset.sum_le_sum
  intro j _
  change BranchConstruction.paperAverage (V j) (B j) (aProj V j z) (bProj V j z) (w j) +
    outerAt V u v z j ≤ _
  exact add_le_add (BranchConstruction.paperAverage_le_portValue (V j) (B j) (aProj V j z) (bProj V j z) (w j)) le_rfl

/-- Every actual maximizer agrees with the inverse-defined multiplier whenever
the latter is feasible; this uses the proved strong dual concavity. -/
theorem maximizing_dual_eq_globalPaperOptimizer (z : Joint V)
    {K : Set (Dual V)} (hK : Convex ℝ K) (hw : WithLp.snd z ∈ K)
    (hstar : globalPaperOptimizer V B z ∈ K)
    (hmax : IsMaxOn (fun w ↦ average V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (atDual V (WithLp.fst z) w)) K (WithLp.snd z)) :
    WithLp.snd z = globalPaperOptimizer V B z := by
  have hsc := (average_dual_stronglyConcave V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) (WithLp.fst z)).strictConcaveOn
      (mul_pos (BranchGeometry.beta_pos ι) (by positivity))
  have hscK := hsc.subset (subset_univ K) hK
  apply hscK.eq_of_isMaxOn hmax _ hw hstar
  intro w _
  exact (average_le_eliminatedValue V B u v z w).trans_eq
    (average_at_globalPaperOptimizer V B u v z).symm

end
end NCConcave16991.GlobalHard
