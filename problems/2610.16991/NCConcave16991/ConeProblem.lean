import NCConcave16991.ConeSmoothFunctions
import NCConcave16991.Problem

/-! # The literal cone construction in the paper's Euclidean problem model

All component functions and gradients are actual functions and derivatives.
The known dual set is a genuine Euclidean ball. Quantitative individual
smoothness is a separate statement, not a field or premise of this constructor.
-/

noncomputable section

namespace NCConcave16991.ConeProblem

open ConeValue Set Metric
open scoped InnerProductSpace BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (M : ℕ)

abbrev primalDimension := Module.finrank ℝ (PrimalBlocks E M)
abbrev dualDimension := Module.finrank ℝ (Blocks E M)

def primalCoordinates : PrimalBlocks E M ≃ₗᵢ[ℝ] PrimalSpace (primalDimension E M) :=
  (stdOrthonormalBasis ℝ (PrimalBlocks E M)).repr

def dualCoordinates : Blocks E M ≃ₗᵢ[ℝ] DualSpace (dualDimension E M) :=
  (stdOrthonormalBasis ℝ (Blocks E M)).repr

def jointCoordinates : JointBlocks E M ≃ₗᵢ[ℝ] JointSpace (primalDimension E M) (dualDimension E M) :=
  (primalCoordinates E M).withLpProdCongr 2 (dualCoordinates E M)

def dualDomain (R : ℝ) (hR : 0 < R) : KnownDualDomain (dualDimension E M) (2 * R) where
  carrier := closedBall 0 R
  nonempty := ⟨0, by simp [hR.le]⟩
  compact := isCompact_closedBall 0 R
  convex := convex_closedBall 0 R
  diameter_bound := by
    intro y hy y' hy'
    have h1 : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    have h2 : ‖y'‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy'
    exact (norm_sub_le _ _).trans (by linarith)

variable {E M} {n : ℕ}

def component (R q : ℝ) (w : Fin n → Fin (M + 1) → E) (i : Fin n)
    (z : JointSpace (primalDimension E M) (dualDimension E M)) : ℝ :=
  jointComponent R q w i ((jointCoordinates E M).symm z)

theorem component_contDiff {q : ℝ} (hq : q ≠ 0) (R : ℝ)
    (w : Fin n → Fin (M + 1) → E) (i : Fin n) :
    ContDiff ℝ ∞ (component R q w i) :=
  (ConeSmooth.component_contDiff hq R w i).comp (jointCoordinates E M).symm.toContinuousLinearEquiv.contDiff

theorem average_formula (hn : 0 < n) (R q : ℝ) (w : Fin n → Fin (M + 1) → E)
    (x : PrimalSpace (primalDimension E M)) (y : DualSpace (dualDimension E M)) :
    componentAverage (component R q w) (jointPoint x y) =
      clockGuard q (sourceMean w) ((primalCoordinates E M).symm x).fst
        ((primalCoordinates E M).symm x).snd +
      R⁻¹ * ⟪ConeValue.residual q (sourceMean w) ((primalCoordinates E M).symm x).fst
        ((primalCoordinates E M).symm x).snd, (dualCoordinates E M).symm y⟫_ℝ := by
  exact component_average hn R q w _ _ _

theorem objective_eq_value (hn : 0 < n) {R : ℝ} (hR : 0 < R) (q : ℝ)
    (w : Fin n → Fin (M + 1) → E) (x : PrimalSpace (primalDimension E M)) :
    primalObjective (dualDomain E M R hR) (component R q w) x =
      primalValue R q w ((primalCoordinates E M).symm x) := by
  unfold primalObjective primalValue dualValue
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ closedBall 0 R at hy
    refine ⟨(dualCoordinates E M).symm y, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hy
    · rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨dualCoordinates E M y, ?_, ?_⟩
    · change dualCoordinates E M y ∈ closedBall 0 R
      simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hy
    · simp only [componentAverage, component, jointPoint, jointComponent, jointCoordinates,
        LinearIsometryEquiv.withLpProdCongr_symm_apply, LinearIsometryEquiv.symm_apply_apply]
      simp only [WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, LinearIsometryEquiv.symm_apply_apply]

def parameters (n : ℕ) (hn : 0 < n) (M : ℕ) (L : ℝ) (hL : 0 < L)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 1 ≤ q) : ProblemParameters where
  n := n
  n_pos := hn
  L := L
  L_pos := hL
  gap := 1 + 91 * (M + 1 : ℕ) * q
  gap_pos := by positivity
  epsilon := 1 / 1000
  epsilon_pos := by norm_num
  diameter := 2 * R
  diameter_nonneg := by positivity

/-- A literal instance of the Section 2 `Problem` type. Its IS/AS class is
not assumed or smuggled into a field; the quantitative class proof is separate. -/
def problem (hn : 0 < n) (L : ℝ) (hL : 0 < L) (R : ℝ) (hR : 0 < R)
    (q : ℝ) (hq : 1 ≤ q) (w : Fin n → Fin (M + 1) → E)
    (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) :
    Problem (parameters n hn M L hL R hR q hq) (primalDimension E M) (dualDimension E M)
      (dualDomain E M R hR) where
  component := component R q w
  componentGradient := fun i ↦ gradient (component R q w i)
  neighborhood := univ
  neighborhood_open := isOpen_univ
  domain_subset := subset_univ _
  gradient_correct := by
    intro i z hz
    exact ((component_contDiff (by linarith : q ≠ 0) R w i).differentiable (by simp) z).hasGradientAt
  average_dual_concave := by
    intro x
    refine ⟨convex_closedBall 0 R, ?_⟩
    intro y hy y' hy' a b ha hb hab
    change a * componentAverage (component R q w) (jointPoint x y) +
      b * componentAverage (component R q w) (jointPoint x y') ≤
        componentAverage (component R q w) (jointPoint x (a • y + b • y'))
    simp only [average_formula hn R q w x, map_add, map_smul, inner_add_right, real_inner_smul_right]
    have he := congrArg (fun t : ℝ ↦ t * clockGuard q (sourceMean w)
      ((primalCoordinates E M).symm x).fst ((primalCoordinates E M).symm x).snd) hab
    nlinarith only [he]
  initialPoint := 0
  value_bddBelow := by
    refine ⟨-91 * (M + 1 : ℕ) * q, ?_⟩
    rintro t ⟨x, rfl⟩
    change -91 * (M + 1 : ℕ) * q ≤ primalObjective (D := 2 * R) (dualDomain E M R hR) (component R q w) x
    rw [objective_eq_value hn hR]
    exact primalValue_lower hn hR hq w hw _
  initial_gap := by
    have hz : primalObjective (dualDomain E M R hR) (component R q w) 0 = 1 := by
      rw [objective_eq_value hn hR, map_zero]
      exact primalValue_zero hn hR (by linarith) w hw
    have hl : -91 * (M + 1 : ℕ) * q ≤
        sInf (range (primalObjective (dualDomain E M R hR) (component R q w))) := by
      apply le_csInf (range_nonempty _)
      rintro t ⟨x, rfl⟩
      rw [objective_eq_value hn hR]
      exact primalValue_lower hn hR hq w hw _
    change primalObjective (D := 2 * R) (dualDomain E M R hR) (component R q w) 0 -
      sInf (range (primalObjective (D := 2 * R) (dualDomain E M R hR) (component R q w))) ≤
        1 + 91 * (M + 1 : ℕ) * q
    rw [hz]
    linarith

end NCConcave16991.ConeProblem
