import NCConcave16991.ConeSmoothGeometry
import NCConcave16991.ConeSmoothClockHessian
import NCConcave16991.ConeSmoothCoupling
import NCConcave16991.ConeSmoothOverlap

/-! # Actual local cone stages and their universal Hessian bound -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial ConeClockGap ConeValue Set
open scoped ContDiff InnerProductSpace BigOperators

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def localStage (n : ℕ) (initial : Bool) (R q : ℝ) (v previous w : E) (x : StageSpace E) : ℝ :=
  localGuardedClock q v (stagePair x) +
    gatedSource n initial R q previous w stageZ stagePrevious stageY x

theorem localGuardedClock_contDiff (q : ℝ) (v : E) : ContDiff ℝ ∞ (localGuardedClock q v) :=
  (clock_contDiff v (pairZ (E := E)).contDiff (pairU (E := E)).contDiff).add
    ((guard_contDiff 3000).comp (pairZ (E := E)).contDiff)

theorem localStage_contDiff (n : ℕ) (initial : Bool) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (v previous w : E) (hprevious : ‖previous‖ = 1) (hw : ‖w‖ = 1) :
    ContDiff ℝ ∞ (localStage n initial R q v previous w) := by
  have hs := gatedSource_localJet n initial hR hq hrel hq2 previous w hprevious hw
    (stageZ (E := E)) stagePrevious stageY stageZ_norm stagePrevious_norm stageY_norm
  exact ((localGuardedClock_contDiff q v).comp (stagePair (E := E)).contDiff).add hs.smooth

theorem localStage_hessian_norm_le (n : ℕ) (initial : Bool) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (v previous w : E) (hv : ‖v‖ = 1) (hprevious : ‖previous‖ = 1) (hw : ‖w‖ = 1)
    (x : StageSpace E) (hx : ‖stageY x‖ ≤ R) :
    ‖fderiv ℝ (fderiv ℝ (localStage n initial R q v previous w)) x‖ ≤
      40000 * (1 + densitySlopeBound) := by
  let f : StageSpace E → ℝ := fun p ↦ localGuardedClock q v (stagePair p)
  let g := gatedSource n initial R q previous w (stageZ (E := E)) stagePrevious stageY
  have hf : ContDiff ℝ ∞ f := (localGuardedClock_contDiff q v).comp (stagePair (E := E)).contDiff
  have hg := gatedSource_localJet n initial hR hq hrel hq2 previous w hprevious hw
    (stageZ (E := E)) stagePrevious stageY stageZ_norm stagePrevious_norm stageY_norm
  have hc := densitySlopeBound_nonneg
  have hfc : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ 36743 + 640 * densitySlopeBound := by
    apply norm_fderiv_le_of_lip' (𝕜 := ℝ) (by positivity)
    exact Filter.Eventually.of_forall (fun y ↦ GlobalHard.fderiv_sub_bound_comp_contraction
      (localGuardedClock q v) ((localGuardedClock_contDiff q v).differentiable (by simp))
      (36743 + 640 * densitySlopeBound) (by positivity) (localGuardedClock_fderiv_sub_bound hq v hv)
      (stagePair (E := E)) stagePair_norm y x)
  have hgc : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ 92 + 32 * densitySlopeBound :=
    gatedSource_hessian_bound n initial hR hq hrel hq2 previous w hprevious hw
      (stageZ (E := E)) stagePrevious stageY stageZ_norm stagePrevious_norm stageY_norm x hx
  change ‖fderiv ℝ (fderiv ℝ (fun p ↦ f p + g p)) x‖ ≤ _
  rw [hessian_add f g (hf.of_le (by simp)) (hg.smooth.of_le (by simp))]
  exact (norm_add_le _ _).trans (by linarith)

variable {M : ℕ}

def previousDirection (v : Fin (M + 1) → E) (j : Fin (M + 1)) : E :=
  if h : j.val = 0 then v 0 else v ⟨j.val - 1, by omega⟩

theorem previousDirection_unit (v : Fin (M + 1) → E) (hv : ∀ j, ‖v j‖ = 1) (j : Fin (M + 1)) :
    ‖previousDirection v j‖ = 1 := by unfold previousDirection; split <;> exact hv _

theorem gate_stageProjection (q : ℝ) (v : Fin (M + 1) → E) (j : Fin (M + 1)) (x : JointBlocks E M) :
    gateFunction (decide (j.val = 0)) q (previousDirection v j) stagePrevious (stageProjection j x) =
      previousGate q v (fun k ↦ x.fst.snd k) j := by
  by_cases hj : j.val = 0
  · simp [gateFunction, previousGate, hj]
  · simp only [gateFunction, hj, decide_false, Bool.false_eq_true, ite_false, previousDirection,
      ↓reduceDIte, previousGate]
    change exitGate q (v ⟨j.val - 1, by omega⟩) (jointPrevious j x) = _
    rw [jointPrevious, dif_neg hj]
    rfl

theorem localStage_projection (n : ℕ) (R q : ℝ) (v b : Fin (M + 1) → E)
    (j : Fin (M + 1)) (x : JointBlocks E M) :
    localStage n (decide (j.val = 0)) R q (v j) (previousDirection v j) (b j) (stageProjection j x) =
      clock q (v j) (x.fst.fst j) (x.fst.snd j) + ConeRadial.guard 3000 (x.fst.fst j) +
        R⁻¹ * (previousGate q v (fun k ↦ x.fst.snd k) j *
          ⟪zeta (x.fst.fst j) - Real.sqrt (n : ℝ) • b j, x.snd j⟫_ℝ) := by
  unfold localStage gatedSource sourceFunction
  rw [gate_stageProjection]
  change (clock q (v j) (x.fst.fst j) (x.fst.snd j) + ConeRadial.guard 3000 (x.fst.fst j)) +
    previousGate q v (fun k ↦ x.fst.snd k) j * (R⁻¹ *
      ⟪zeta (x.fst.fst j) - Real.sqrt (n : ℝ) • b j, x.snd j⟫_ℝ) = _
  ring

theorem jointComponent_eq_stages {n : ℕ} (R q : ℝ) (w : Fin n → Fin (M + 1) → E) (i : Fin n) :
    jointComponent R q w i = fun x ↦ ∑ j, localStage n (decide (j.val = 0)) R q
      (sourceMean w j) (previousDirection (sourceMean w) j) (w i j) (stageProjection j x) := by
  funext x
  simp only [localStage_projection, jointComponent, component, clockGuard,
    Finset.sum_add_distrib, Finset.mul_sum]

def individualConstant : ℝ := 100000 * (1 + densitySlopeBound)

theorem individualConstant_pos : 0 < individualConstant := by
  have hc := densitySlopeBound_nonneg
  unfold individualConstant
  positivity

theorem jointComponent_hessian_norm_le {n : ℕ} (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (i : Fin n) (x : JointBlocks E M) (hx : ‖x.snd‖ ≤ R) :
    ‖fderiv ℝ (fderiv ℝ (jointComponent R q w i)) x‖ ≤ individualConstant := by
  have hv := sourceMean_unit hn w hw
  let g : Fin (M + 1) → StageSpace E → ℝ := fun j ↦ localStage n (decide (j.val = 0)) R q
    (sourceMean w j) (previousDirection (sourceMean w) j) (w i j)
  have hg (j : Fin (M + 1)) : ContDiff ℝ 2 (g j) :=
    (localStage_contDiff n _ hR hq hrel hq2 _ _ _
      (previousDirection_unit (sourceMean w) hv j) ((hw j).norm_eq_one i)).of_le (by simp)
  rw [jointComponent_eq_stages]
  have hc := densitySlopeBound_nonneg
  have hh := hessian_linear_family_bound g hg (stageProjection (E := E) (M := M))
    (C := 40000 * (1 + densitySlopeBound)) (load := 2) (by positivity) (by norm_num) x
    (fun j ↦ localStage_hessian_norm_le n _ hR hq hrel hq2 _ _ _ (hv j)
      (previousDirection_unit (sourceMean w) hv j) ((hw j).norm_eq_one i) _
      ((PiLp.norm_apply_le (p := 2) x.snd j).trans hx)) stageProjection_energy_bound
  exact hh.trans (by unfold individualConstant; nlinarith)

end NCConcave16991.ConeSmooth
