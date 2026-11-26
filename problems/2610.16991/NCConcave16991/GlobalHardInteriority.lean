import NCConcave16991.GlobalHardConnectorBound
import NCConcave16991.GlobalHardElimination

/-! # Dual elimination at actual small-gradient maximizing witnesses -/

namespace NCConcave16991.GlobalHard
noncomputable section
open Set
open scoped InnerProductSpace

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
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

theorem paper_maximizer_eq_optimizer_of_not_all_high (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (hex : ∃ j, score V v j z < 1)
    (hw : WithLp.snd z ∈ Metric.closedBall 0 (publicDualRadius (Fintype.card ι) (m + 2)))
    (hmax : IsMaxOn (fun w ↦ average V B u v (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (atDual V (WithLp.fst z) w))
      (Metric.closedBall 0 (publicDualRadius (Fintype.card ι) (m + 2))) (WithLp.snd z)) :
    ‖connectorTuple V z‖ ≤ 43 / 4 ∧ WithLp.snd z = globalPaperOptimizer V B z := by
  obtain ⟨f, hhigh, hlow⟩ := average_frontier V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z hu hv hg hex
  have hzero : (0 : Dual V) ∈ Metric.closedBall 0 (publicDualRadius (Fintype.card ι) (m + 2)) := by
    simp only [Metric.mem_closedBall, dist_self]
    exact publicDualRadius_nonneg _ _
  have hc := connector_norm_bound_of_frontier V B u v (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) z (EndpointConstants.endpointD_bounds m).1.le (by positivity)
    hu hv hg f hhigh hlow (convex_closedBall _ _) hzero hw hmax
  refine ⟨hc, ?_⟩
  apply maximizing_dual_eq_globalPaperOptimizer V B u v z (convex_closedBall _ _) hw _ hmax
  exact Metric.ball_subset_closedBall (globalPaperOptimizer_mem_public_ball V B z hc)

end
end NCConcave16991.GlobalHard
