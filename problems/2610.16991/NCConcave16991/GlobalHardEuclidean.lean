import NCConcave16991.GlobalHardPaper
import NCConcave16991.GlobalHardDual
import NCConcave16991.Problem

/-! # Literal global instance in the paper's Euclidean oracle coordinates -/

namespace NCConcave16991.GlobalHardEuclidean

noncomputable section

open Set Metric GlobalHard
open scoped InnerProductSpace BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]

abbrev primalDimension := Module.finrank ℝ (GlobalHard.Primal V)
abbrev dualDimension := Module.finrank ℝ (GlobalHard.Dual V)

def primalCoordinates : GlobalHard.Primal V ≃ₗᵢ[ℝ] PrimalSpace (primalDimension V) :=
  (stdOrthonormalBasis ℝ (GlobalHard.Primal V)).repr

def dualCoordinates : GlobalHard.Dual V ≃ₗᵢ[ℝ] DualSpace (dualDimension V) :=
  (stdOrthonormalBasis ℝ (GlobalHard.Dual V)).repr

def jointCoordinates : GlobalHard.Joint V ≃ₗᵢ[ℝ] JointSpace (primalDimension V) (dualDimension V) :=
  (primalCoordinates V).withLpProdCongr 2 (dualCoordinates V)

def dualDomain (R : ℝ) (hR : 0 < R) : KnownDualDomain (dualDimension V) (2 * R) where
  carrier := closedBall 0 R
  nonempty := ⟨0, by simp [hR.le]⟩
  compact := isCompact_closedBall 0 R
  convex := convex_closedBall 0 R
  diameter_bound := by
    intro y hy y' hy'
    have h1 : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    have h2 : ‖y'‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy'
    exact (norm_sub_le _ _).trans (by linarith)

variable {n : ℕ}
variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def component (d r μ : ℝ) (i : Fin n)
    (z : JointSpace (primalDimension V) (dualDimension V)) : ℝ :=
  GlobalHard.component V B u v d r μ i ((jointCoordinates V).symm z)

theorem component_contDiff (hn : 0 < n) (d r μ : ℝ) (i : Fin n) :
    ContDiff ℝ ∞ (component V B u v d r μ i) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (GlobalHard.component_contDiff V B u v d r μ i).comp
    (jointCoordinates V).symm.toContinuousLinearEquiv.contDiff

theorem average_formula (hn : 0 < n) (d r μ : ℝ)
    (x : PrimalSpace (primalDimension V)) (y : DualSpace (dualDimension V)) :
    componentAverage (component V B u v d r μ) (jointPoint x y) =
      GlobalHard.average V B u v d r μ
        (atDual V ((primalCoordinates V).symm x) ((dualCoordinates V).symm y)) := by
  simp only [componentAverage, component, GlobalHard.average, Fintype.card_fin, one_div,
    jointCoordinates, jointPoint, LinearIsometryEquiv.withLpProdCongr_symm_apply, atDual]
  rfl

theorem objective_eq_value (hn : 0 < n) (d r μ : ℝ) {R : ℝ} (hR : 0 < R)
    (x : PrimalSpace (primalDimension V)) :
    primalObjective (dualDomain V R hR) (component V B u v d r μ) x =
      GlobalHard.value V B u v d r μ R ((primalCoordinates V).symm x) := by
  unfold primalObjective GlobalHard.value
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ closedBall 0 R at hy
    refine ⟨(dualCoordinates V).symm y, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hy
    · exact (average_formula V B u v hn d r μ x y).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨dualCoordinates V y, ?_, ?_⟩
    · change dualCoordinates V y ∈ closedBall 0 R
      simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hy
    · change componentAverage (component V B u v d r μ) (jointPoint x (dualCoordinates V y)) = _
      rw [average_formula V B u v hn d r μ]
      simp only [LinearIsometryEquiv.symm_apply_apply]

theorem component_gradient_sub_bound (hn : 0 < n) (d r μ : ℝ)
    (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (i : Fin n)
    (x y : JointSpace (primalDimension V) (dualDimension V)) :
    ‖gradient (component V B u v d r μ i) x - gradient (component V B u v d r μ i) y‖ ≤
      100000000 * ‖x - y‖ := by
  letI : NeZero n := ⟨hn.ne'⟩
  let P := (jointCoordinates V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound P (by norm_num)
    intro z
    change ‖(jointCoordinates V).symm z‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using (jointCoordinates V).symm.norm_map z |>.le
  have hh := fderiv_sub_bound_comp_contraction (GlobalHard.component V B u v d r μ i)
    ((GlobalHard.component_contDiff V B u v d r μ i).differentiable (by simp))
    25609776 (by norm_num)
    (GlobalHard.component_fderiv_sub_bound V B u v d r μ hd hr hμ0 hμ1 hu hv i) P hP x y
  have he : ‖gradient (component V B u v d r μ i) x - gradient (component V B u v d r μ i) y‖ =
      ‖fderiv ℝ (component V B u v d r μ i) x - fderiv ℝ (component V B u v d r μ i) y‖ := by
    rw [← (InnerProductSpace.toDual ℝ (JointSpace (primalDimension V) (dualDimension V))).norm_map,
      map_sub, toDual_gradient, toDual_gradient]
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num : (25609776 : ℝ) ≤ 100000000) (norm_nonneg _))

def parameters (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (R : ℝ) (hR : 0 < R) : ProblemParameters where
  n := n
  n_pos := hn
  L := 100000000
  L_pos := by norm_num
  gap := 31000 * M
  gap_pos := mul_pos (by norm_num) (by exact_mod_cast hM)
  epsilon := 1 / 40
  epsilon_pos := by norm_num
  diameter := 2 * R
  diameter_nonneg := by positivity

theorem objective_bddBelow (hn : 0 < n) (d r μ : ℝ) (hd : 0 ≤ d)
    {R : ℝ} (hR : 0 < R) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    BddBelow (range (primalObjective (dualDomain V R hR) (component V B u v d r μ))) := by
  letI : NeZero n := ⟨hn.ne'⟩
  refine ⟨-31000 * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [objective_eq_value V B u v hn d r μ hR x]
  exact GlobalHard.value_lower V B u v d r μ R hd hR.le hu hv _

theorem objective_initial_gap (hn : 0 < n) (d r μ : ℝ) (hd : 0 ≤ d) (hμ : 0 ≤ μ)
    {R : ℝ} (hR : 0 < R) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    primalObjective (dualDomain V R hR) (component V B u v d r μ) 0 -
      sInf (range (primalObjective (dualDomain V R hR) (component V B u v d r μ))) ≤ 31000 * M := by
  letI : NeZero n := ⟨hn.ne'⟩
  have he : range (primalObjective (dualDomain V R hR) (component V B u v d r μ)) =
      range (GlobalHard.value V B u v d r μ R) := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(primalCoordinates V).symm x, (objective_eq_value V B u v hn d r μ hR x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨primalCoordinates V x, ?_⟩
      rw [objective_eq_value V B u v hn d r μ hR, LinearIsometryEquiv.symm_apply_apply]
  rw [he, objective_eq_value V B u v hn d r μ hR, map_zero]
  exact GlobalHard.initial_gap V B u v d r μ R hd hμ hR.le hu hv

/-- The literal finite-sum instance in the exact Euclidean oracle model.
Its class proof below is derived from the explicit global calculus. -/
def problem (hn : 0 < n) (hM : 0 < M) (d r μ : ℝ) (hd : 0 ≤ d) (hμ : 0 ≤ μ)
    (R : ℝ) (hR : 0 < R) (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    Problem (parameters n hn M hM R hR) (primalDimension V) (dualDimension V) (dualDomain V R hR) := by
  letI : NeZero n := ⟨hn.ne'⟩
  refine {
    component := component V B u v d r μ
    componentGradient := fun i ↦ gradient (component V B u v d r μ i)
    neighborhood := univ
    neighborhood_open := isOpen_univ
    domain_subset := subset_univ _
    gradient_correct := fun i z _ ↦ ((component_contDiff V B u v hn d r μ i).differentiable (by simp) z).hasGradientAt
    average_dual_concave := ?_
    initialPoint := 0
    value_bddBelow := objective_bddBelow V B u v hn d r μ hd hR hu hv
    initial_gap := objective_initial_gap V B u v hn d r μ hd hμ hR hu hv }
  intro x
  refine ⟨(dualDomain V R hR).convex, ?_⟩
  intro y hy y' hy' a b ha hb hab
  change a * componentAverage (component V B u v d r μ) (jointPoint x y) +
    b * componentAverage (component V B u v d r μ) (jointPoint x y') ≤
      componentAverage (component V B u v d r μ) (jointPoint x (a • y + b • y'))
  simp only [average_formula V B u v hn d r μ, map_add, map_smul]
  exact (GlobalHard.average_dual_concave V B u v d r μ hμ ((primalCoordinates V).symm x)).2
    (mem_univ _) (mem_univ _) ha hb hab

theorem problem_individualSmooth (hn : 0 < n) (hM : 0 < M) (d r μ : ℝ)
    (hd0 : 0 ≤ d) (hμ0 : 0 ≤ μ) (R : ℝ) (hR : 0 < R)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1) (hμ1 : μ ≤ 1) :
    (problem V B u v hn hM d r μ hd0 hμ0 R hR hu hv).individualSmooth := by
  intro i x hx y hy
  exact component_gradient_sub_bound V B u v hn d r μ hd hr hμ0 hμ1 hu hv i x y

end

end NCConcave16991.GlobalHardEuclidean
