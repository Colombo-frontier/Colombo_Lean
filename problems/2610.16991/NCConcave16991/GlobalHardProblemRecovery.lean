import NCConcave16991.GlobalHardPaperProblem
import NCConcave16991.GlobalHardTerminal
import NCConcave16991.ConeProblemRecovery

/-! # Actual Euclidean maximizing saddles force every literal branch score high -/

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace NCConcave16991.GlobalHardEuclidean

open GlobalHard

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {n M m : ℕ} [NeZero n] (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
  (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

theorem paper_actual_maximizer_all_high (hn : 0 < n) (hM : 0 < M)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hprop : ∀ j, v j = BranchConstruction.terminalTransport (V j) (B j) (u j))
    (x : PrimalSpace (primalDimension V)) (y : DualSpace (dualDimension V))
    (hy : y ∈ (paperDualDomain V hn).carrier)
    (hmax : componentAverage (paperProblem V B u v hn hM hu hv).component (jointPoint x y) =
      primalObjective (paperDualDomain V hn) (paperProblem V B u v hn hM hu hv).component x)
    (hsmall : ‖Accelerated.primalMeanGradient (paperProblem V B u v hn hM hu hv) x y‖ ≤ 1 / 20) :
    ∀ j, 1 ≤ score V v j (atDual V ((primalCoordinates V).symm x) ((dualCoordinates V).symm y)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let P := paperProblem V B u v hn hM hu hv
  let xp := (primalCoordinates V).symm x
  let yp := (dualCoordinates V).symm y
  let d := EndpointConstants.endpointD m
  let r := Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m)
  let μ := 1 / ((m : ℝ) + 2) ^ 2
  have hsection := P.hasGradientAt_primal_section x y hy
  have hgrad := ConeProblem.isometry_comp_hasGradientAt (primalCoordinates V)
    (f := fun a ↦ componentAverage P.component (jointPoint a y))
    (g := Accelerated.primalMeanGradient P x y) (x := xp)
    (by simpa only [Accelerated.primalMeanGradient, xp, LinearIsometryEquiv.apply_symm_apply] using hsection)
  have hfun : (fun a : GlobalHard.Primal V ↦ componentAverage P.component
      (jointPoint (primalCoordinates V a) y)) = primalAverageSection V B u v d r μ yp := by
    funext a
    change componentAverage (component V B u v d r μ) (jointPoint (primalCoordinates V a) y) = _
    rw [average_formula V B u v hn d r μ]
    simp only [LinearIsometryEquiv.symm_apply_apply, primalAverageSection, yp, atDual]
  rw [hfun] at hgrad
  have hg : ‖gradient (primalAverageSection V B u v d r μ yp) xp‖ ≤ 1 / 20 := by
    rw [hgrad.gradient, LinearIsometryEquiv.norm_map]
    exact hsmall
  have hyp : yp ∈ closedBall 0 (publicDualRadius n (m + 2)) := by
    have hnorm : ‖y‖ ≤ publicDualRadius n (m + 2) := by
      simpa only [paperDualDomain, dualDomain, mem_closedBall, dist_zero_right] using hy
    simpa only [yp, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hnorm
  have hrawmax : IsMaxOn (fun w ↦ average V B u v d r μ (atDual V xp w))
      (closedBall 0 (publicDualRadius n (m + 2))) yp := by
    intro w hw
    have hwy : dualCoordinates V w ∈ (paperDualDomain V hn).carrier := by
      simpa only [paperDualDomain, dualDomain, mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map] using hw
    have hh := componentAverage_le_primalObjective P x (dualCoordinates V w) hwy
    rw [← hmax] at hh
    change componentAverage (component V B u v d r μ) (jointPoint x (dualCoordinates V w)) ≤
      componentAverage (component V B u v d r μ) (jointPoint x y) at hh
    rw [average_formula V B u v hn d r μ, average_formula V B u v hn d r μ] at hh
    simpa only [xp, yp, LinearIsometryEquiv.symm_apply_apply, Set.mem_setOf_eq] using hh
  exact maximizing_small_primal_gradient_all_high V B u v (atDual V xp yp) hu hv hprop hg
    (by simpa only [Fintype.card_fin, atDual, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp] using hyp)
    (by simpa only [Fintype.card_fin, atDual, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp] using hrawmax)

end NCConcave16991.GlobalHardEuclidean
