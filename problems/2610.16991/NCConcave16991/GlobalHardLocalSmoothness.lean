import NCConcave16991.GlobalHardSupport
import NCConcave16991.GlobalHardOuterJets
import NCConcave16991.GlobalHardDerivativeRules

/-! # Actual dimension-free local derivative bound for every complete stage -/

namespace NCConcave16991.GlobalHard

noncomputable section

open scoped InnerProductSpace ContDiff

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem stageEntrance_jet (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (j : Fin M) :
    JetBound (fun z : Joint V ↦ entrance (u j) (precedingScore V v j z)
      (stateScore (v j) (stateProj V j z)) (aProj V j z)) 168 3364 107684 := by
  by_cases hj : j.val = 0
  · simpa only [precedingScore_of_zero V v j hj] using
      initial_entrance_score_jet (v j) (hv j) (u j) (hu j) (stateProj V j) (stateProj_norm V j)
        (aProj V j) (aProj_norm V j)
  · simpa only [precedingScore_of_positive V v j hj] using
      entrance_score_jet (v (predecessor j hj)) (hv _) (v j) (hv j) (u j) (hu j)
        (stateProj V (predecessor j hj)) (stateProj_norm V _) (stateProj V j) (stateProj_norm V j)
        (aProj V j) (aProj_norm V j)

theorem stageExit_jet (hv : ∀ j, ‖v j‖ = 1) (j : Fin M) :
    JetBound (fun z : Joint V ↦ exit (precedingScore V v j z)
      (stateScore (v j) (stateProj V j z)) (stateProj V j z) (bProj V j z)) 840 16862 540186 := by
  by_cases hj : j.val = 0
  · simpa only [precedingScore_of_zero V v j hj] using
      initial_exit_score_jet (v j) (hv j) (stateProj V j) (bProj V j) (stateProj_norm V j) (bProj_norm V j)
  · simpa only [precedingScore_of_positive V v j hj] using
      exit_score_jet (v (predecessor j hj)) (hv _) (v j) (hv j)
        (stateProj V (predecessor j hj)) (stateProj_norm V _) (stateProj V j) (bProj V j)
        (stateProj_norm V j) (bProj_norm V j)

theorem stageCoupling_jet (hv : ∀ j, ‖v j‖ = 1) (j : Fin M) :
    JetBound (fun z : Joint V ↦ stateCoupling (precedingScore V v j z)
      (stateScore (v j) (stateProj V j z))) 602 12212 395256 := by
  by_cases hj : j.val = 0
  · have hh := (JetBound.const (E := Joint V) (0 : ℝ)).weaken 602 12212 395256
      (by norm_num) (by norm_num) (by norm_num)
    simpa only [precedingScore_of_zero V v j hj, initial_stateCoupling_zero] using hh
  · simpa only [precedingScore_of_positive V v j hj] using
      stateCoupling_score_jet (v (predecessor j hj)) (hv _) (v j) (hv j)
        (stateProj V (predecessor j hj)) (stateProj_norm V _) (stateProj V j) (stateProj_norm V j)

theorem stageComponent_contDiff (d r μ : ℝ) (i : ι) (j : Fin M) :
    ContDiff ℝ ∞ (stageComponent V B u v d r μ i j) :=
  (pipe_contDiff V B d r μ i j).add
    (outerStage_contDiff (u j) (v j) _ _ _ _ (precedingScore_contDiff V v j)
      (stateProj V j).contDiff (aProj V j).contDiff (bProj V j).contDiff)

theorem pipe_fderiv_sub_bound (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (i : ι) (j : Fin M) (x y : Joint V) :
    ‖fderiv ℝ (fun z ↦ PipeSmoothness.component (B j) d r μ i (pipeProj V j z)) x -
      fderiv ℝ (fun z ↦ PipeSmoothness.component (B j) d r μ i (pipeProj V j z)) y‖ ≤ 8 * ‖x - y‖ := by
  apply fderiv_sub_bound_comp_contraction _
    (fun z ↦ (PipeSmoothness.component_hasGradientAt (B j) d r μ i z).differentiableAt)
    8 (by norm_num) _ (pipeProj V j) (pipeProj_norm V j) x y
  intro a b
  have hh := PipeSmoothness.component_gradient_lipschitz (B j) d r μ hd hr hμ0 hμ1 i a b
  have he : ‖gradient (PipeSmoothness.component (B j) d r μ i) a -
      gradient (PipeSmoothness.component (B j) d r μ i) b‖ =
      ‖fderiv ℝ (PipeSmoothness.component (B j) d r μ i) a -
        fderiv ℝ (PipeSmoothness.component (B j) d r μ i) b‖ := by
    rw [← (InnerProductSpace.toDual ℝ (PipeSmoothness.Joint (V j))).norm_map,
      map_sub, toDual_gradient, toDual_gradient]
  rwa [he] at hh

theorem stageComponent_fderiv_sub_bound (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (i : ι) (j : Fin M) (x y : Joint V) :
    ‖fderiv ℝ (stageComponent V B u v d r μ i j) x -
      fderiv ℝ (stageComponent V B u v d r μ i j) y‖ ≤ 12804888 * ‖x - y‖ := by
  let en := fun z : Joint V ↦ entrance (u j) (precedingScore V v j z) (stateScore (v j) (stateProj V j z)) (aProj V j z)
  let ex := fun z : Joint V ↦ exit (precedingScore V v j z) (stateScore (v j) (stateProj V j z)) (stateProj V j z) (bProj V j z)
  let st := fun z : Joint V ↦ stateCoupling (precedingScore V v j z) (stateScore (v j) (stateProj V j z))
  let pe := fun z : Joint V ↦ statePenalty (v j) (stateProj V j z)
  let pp := fun z : Joint V ↦ PipeSmoothness.component (B j) d r μ i (pipeProj V j z)
  have hen : JetBound en 168 3364 107684 := stageEntrance_jet V u v hu hv j
  have hex : JetBound ex 840 16862 540186 := stageExit_jet V v hv j
  have hst : JetBound st 602 12212 395256 := stageCoupling_jet V v hv j
  have hpe : ContDiff ℝ ∞ pe := (statePenalty_contDiff (v j)).comp (stateProj V j).contDiff
  have hpp : ContDiff ℝ ∞ pp := pipe_contDiff V B d r μ i j
  have hpec : ∀ a b, ‖fderiv ℝ pe a - fderiv ℝ pe b‖ ≤ 11761754 * ‖a - b‖ :=
    fderiv_sub_bound_comp_contraction _ ((statePenalty_contDiff (v j)).differentiable (by simp))
      11761754 (by norm_num) (statePenalty_fderiv_sub_bound (v j) (hv j)) (stateProj V j) (stateProj_norm V j)
  have hppc := pipe_fderiv_sub_bound V B d r μ hd hr hμ0 hμ1 i j
  have h1 := fderiv_sub_bound_add en ex (hen.smooth.differentiable (by simp)) (hex.smooth.differentiable (by simp))
    107684 540186 hen.second hex.second
  have h2 := fderiv_sub_bound_add (fun z ↦ en z + ex z) st
    ((hen.smooth.add hex.smooth).differentiable (by simp)) (hst.smooth.differentiable (by simp))
    (107684 + 540186) 395256 h1 hst.second
  have h3 := fderiv_sub_bound_add (fun z ↦ en z + ex z + st z) pe
    (((hen.smooth.add hex.smooth).add hst.smooth).differentiable (by simp)) (hpe.differentiable (by simp))
    (107684 + 540186 + 395256) 11761754 h2 hpec
  have h4 := fderiv_sub_bound_add pp (fun z ↦ en z + ex z + st z + pe z)
    (hpp.differentiable (by simp)) ((((hen.smooth.add hex.smooth).add hst.smooth).add hpe).differentiable (by simp))
    8 (107684 + 540186 + 395256 + 11761754) hppc h3 x y
  convert h4 using 1 <;> first | rfl | norm_num

end

end NCConcave16991.GlobalHard
