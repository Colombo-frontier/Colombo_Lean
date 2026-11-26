import NCConcave16991.GlobalHardProblemRecovery
import NCConcave16991.GlobalHardCoordinates

/-! # Arbitrary stationary outputs correlate with every terminal source -/

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace NCConcave16991.GlobalHardEuclidean

open GlobalHard LocalizationRadial

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {n M m : ℕ} (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]

def primalStateProjection (j : Fin M) : GlobalHard.Primal V →L[ℝ] V j (Fin.last (m + 1)) :=
  (WithLp.fstL 2 ℝ _ _).comp (PiLp.proj 2 (GlobalHard.PrimalStage V) j)

theorem primalStateProjection_norm (j : Fin M) : ‖primalStateProjection V j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact ((WithLp.norm_fst_le (p := 2) _ (x j)).trans (PiLp.norm_apply_le x j)).trans_eq (one_mul _).symm

theorem primalStateProjection_sub_bound (j : Fin M) (x y : GlobalHard.Primal V) :
    ‖primalStateProjection V j x - primalStateProjection V j y‖ ≤ ‖x - y‖ := by
  rw [← map_sub]
  exact ((primalStateProjection V j).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (primalStateProjection_norm V j) (norm_nonneg _)).trans_eq (one_mul _))

def returnedSourceProbe (j : Fin M) (c : PrimalSpace (primalDimension V)) : V j (Fin.last (m + 1)) :=
  (1 / 20 : ℝ) • radialCap 10 (primalStateProjection V j ((primalCoordinates V).symm c))

theorem returnedSourceProbe_norm_le (j : Fin M) (c : PrimalSpace (primalDimension V)) :
    ‖returnedSourceProbe V j c‖ ≤ 1 := by
  have hh := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 10)
    (primalStateProjection V j ((primalCoordinates V).symm c))).trans (min_le_right _ _)
  norm_num at hh
  unfold returnedSourceProbe
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

variable [NeZero n] (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

theorem stationary_output_score_lower (hn : 0 < n) (hM : 0 < M)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hprop : ∀ j, v j = BranchConstruction.terminalTransport (V j) (B j) (u j))
    (c : PrimalSpace (primalDimension V))
    (hc : StationaryOutput (paperProblem V B u v hn hM hu hv) c) :
    ∀ j, 3 / 4 ≤ stateScore (v j) (primalStateProjection V j ((primalCoordinates V).symm c)) := by
  let P := paperProblem V B u v hn hM hu hv
  have hAS := paperProblem_averagedSmooth V B u v hn hM hu hv
  let x := proximalMap (paperParameters n hn M hM m).L_pos (P.primal_continuous hAS) P.value_bddBelow c
  obtain ⟨y,hy,hmax,hsmall,hdisp⟩ := stationaryOutput_proximal_witness P hAS c hc
  change componentAverage P.component (jointPoint x y) = primalObjective (paperDualDomain V hn) P.component x at hmax
  change ‖Accelerated.primalMeanGradient P x y‖ ≤ (paperParameters n hn M hM m).epsilon at hsmall
  change ‖x - c‖ ≤ (paperParameters n hn M hM m).epsilon / (2 * (paperParameters n hn M hM m).L) at hdisp
  have hg : ‖Accelerated.primalMeanGradient P x y‖ ≤ 1 / 20 :=
    hsmall.trans (by norm_num [paperParameters, parameters])
  have hall := paper_actual_maximizer_all_high V B u v hn hM hu hv hprop x y hy hmax hg
  have hdist : ‖(primalCoordinates V).symm x - (primalCoordinates V).symm c‖ ≤ 1 / 4 := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact hdisp.trans (by norm_num [paperParameters, parameters])
  intro j
  have hs := (primalStateProjection_sub_bound V j ((primalCoordinates V).symm x)
    ((primalCoordinates V).symm c)).trans hdist
  have hl := (radialCap_score_lipschitz (by norm_num : (0 : ℝ) < 10) (v j) (hv j)
    (primalStateProjection V j ((primalCoordinates V).symm x))
    (primalStateProjection V j ((primalCoordinates V).symm c))).trans hs
  have hh := hall j
  change 1 ≤ stateScore (v j) (primalStateProjection V j ((primalCoordinates V).symm x)) at hh
  change |stateScore (v j) (primalStateProjection V j ((primalCoordinates V).symm x)) -
    stateScore (v j) (primalStateProjection V j ((primalCoordinates V).symm c))| ≤ 1 / 4 at hl
  linarith [(abs_le.mp hl).2]

/-- This bounded probe is computed from the original returned point alone;
the true proximal point and maximizing multiplier are only proof witnesses. -/
theorem stationary_output_source_probe (hn : 0 < n) (hM : 0 < M)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hprop : ∀ j, v j = BranchConstruction.terminalTransport (V j) (B j) (u j))
    (c : PrimalSpace (primalDimension V))
    (hc : StationaryOutput (paperProblem V B u v hn hM hu hv) c) :
    ∀ j, 1 / 40 ≤ ⟪v j, returnedSourceProbe V j c⟫_ℝ := by
  intro j
  have hs := stationary_output_score_lower V B u v hn hM hu hv hprop c hc j
  rw [returnedSourceProbe, real_inner_smul_right]
  change 1 / 40 ≤ (1 / 20 : ℝ) * stateScore (v j)
    (primalStateProjection V j ((primalCoordinates V).symm c))
  linarith

end NCConcave16991.GlobalHardEuclidean
