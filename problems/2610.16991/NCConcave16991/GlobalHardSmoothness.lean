import NCConcave16991.GlobalHardLocalSmoothness

/-! # Global dimension-free smoothness of the literal hard components -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set
open scoped BigOperators InnerProductSpace ContDiff

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def regroupCLM : Blocks V →L[ℝ] Joint V := (regroup V).toContinuousLinearEquiv.toContinuousLinearMap

theorem regroupCLM_norm : ‖regroupCLM V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (regroupCLM V) (by norm_num)
  intro z
  change ‖regroup V z‖ ≤ 1 * ‖z‖
  simpa only [one_mul] using (regroup V).norm_map z |>.le

theorem regrouped_hessian_bound (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (i : ι) (z : Blocks V) :
    ‖fderiv ℝ (fderiv ℝ (fun x ↦ component V B u v d r μ i (regroup V x))) z‖ ≤ 25609776 := by
  let g := fun j : Fin M ↦ fun x : Blocks V ↦ stageComponent V B u v d r μ i j (regroup V x)
  have hg (j : Fin M) : ContDiff ℝ 2 (g j) :=
    ((stageComponent_contDiff V B u v d r μ i j).comp (regroupCLM V).contDiff).of_le (by simp)
  have hlocal (j : Fin M) (x : Blocks V) : ‖fderiv ℝ (fderiv ℝ (g j)) x‖ ≤ 12804888 := by
    apply norm_fderiv_le_of_lip' (𝕜 := ℝ) (by norm_num : (0 : ℝ) ≤ 12804888)
    apply Filter.Eventually.of_forall
    intro y
    exact fderiv_sub_bound_comp_contraction _
      ((stageComponent_contDiff V B u v d r μ i j).differentiable (by simp))
      12804888 (by norm_num) (stageComponent_fderiv_sub_bound V B u v d r μ hd hr hμ0 hμ1 hu hv i j)
      (regroupCLM V) (regroupCLM_norm V) y x
  have hh := HessianOverlap.actual_hessian_overlap_degree_bound support g hg
    12804888 (by norm_num) 2 hlocal support_degree z
  have he : (fun x : Blocks V ↦ ∑ j, g j (HessianOverlap.blockProjection (support j) x)) =
      fun x ↦ component V B u v d r μ i (regroup V x) := by
    funext x
    exact (component_eq_supported_sum V B u v d r μ i x).symm
  rw [he] at hh
  norm_num at hh
  exact hh

theorem regrouped_fderiv_sub_bound (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (i : ι) (x y : Blocks V) :
    ‖fderiv ℝ (fun z ↦ component V B u v d r μ i (regroup V z)) x -
      fderiv ℝ (fun z ↦ component V B u v d r μ i (regroup V z)) y‖ ≤ 25609776 * ‖x - y‖ := by
  have hs : ContDiff ℝ 2 (fun z : Blocks V ↦ component V B u v d r μ i (regroup V z)) :=
    ((component_contDiff V B u v d r μ i).comp (regroupCLM V).contDiff).of_le (by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (fun z _ ↦ (hs.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z)
    (fun z _ ↦ regrouped_hessian_bound V B u v d r μ hd hr hμ0 hμ1 hu hv i z)
    convex_univ (mem_univ y) (mem_univ x)

theorem component_fderiv_sub_bound (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (i : ι) (x y : Joint V) :
    ‖fderiv ℝ (component V B u v d r μ i) x - fderiv ℝ (component V B u v d r μ i) y‖ ≤
      25609776 * ‖x - y‖ := by
  let Q : Joint V →L[ℝ] Blocks V := (regroup V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hQ : ‖Q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound Q (by norm_num)
    intro z
    change ‖(regroup V).symm z‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using (regroup V).symm.norm_map z |>.le
  have hh := fderiv_sub_bound_comp_contraction
    (fun z : Blocks V ↦ component V B u v d r μ i (regroup V z))
    (((component_contDiff V B u v d r μ i).comp (regroupCLM V).contDiff).differentiable (by simp))
    25609776 (by norm_num) (regrouped_fderiv_sub_bound V B u v d r μ hd hr hμ0 hμ1 hu hv i) Q hQ x y
  have he : (fun z : Joint V ↦ component V B u v d r μ i (regroup V (Q z))) = component V B u v d r μ i := by
    funext z
    exact congrArg (component V B u v d r μ i) ((regroup V).apply_symm_apply z)
  rwa [he] at hh

/-- Every literal selected global component is jointly 10^8-smooth,
uniformly in all dimensions, stages, layers, components and branch rotations. -/
theorem component_global_smooth (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (i : ι) (x y : Joint V) :
    ‖gradient (component V B u v d r μ i) x - gradient (component V B u v d r μ i) y‖ ≤
      100000000 * ‖x - y‖ := by
  have he : ‖gradient (component V B u v d r μ i) x - gradient (component V B u v d r μ i) y‖ =
      ‖fderiv ℝ (component V B u v d r μ i) x - fderiv ℝ (component V B u v d r μ i) y‖ := by
    rw [← (InnerProductSpace.toDual ℝ (Joint V)).norm_map, map_sub, toDual_gradient, toDual_gradient]
  rw [he]
  exact (component_fderiv_sub_bound V B u v d r μ hd hr hμ0 hμ1 hu hv i x y).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (25609776 : ℝ) ≤ 100000000) (norm_nonneg _))

end

end NCConcave16991.GlobalHard
