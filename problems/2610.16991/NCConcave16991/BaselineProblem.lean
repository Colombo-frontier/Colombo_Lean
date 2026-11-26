import NCConcave16991.BaselineHilbert
import NCConcave16991.Problem

/-! # The hidden quadratic family in the literal Section 2 problem model -/

open Set
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.BaselineProblem

noncomputable section

def dualDomain (p : ProblemParameters) : KnownDualDomain 0 p.diameter where
  carrier := {0}
  nonempty := ⟨0, mem_singleton 0⟩
  compact := isCompact_singleton
  convex := convex_singleton 0
  diameter_bound := by
    intro y hy y' hy'
    simp only [mem_singleton_iff] at hy hy'
    subst y
    subst y'
    simpa using p.diameter_nonneg

def direction : PrimalSpace 1 := EuclideanSpace.single (0 : Fin 1) 1

theorem direction_norm : ‖direction‖ = 1 := by simp [direction]

def tilt (a : ℝ) : JointSpace 1 0 := jointPoint (a • direction) 0

def component (p : ProblemParameters) (a : ℝ) (j i : Fin p.n) (z : JointSpace 1 0) : ℝ :=
  BaselineHilbert.value p.L (if i=j then (p.n : ℝ) • tilt a else 0) z

def componentGradient (p : ProblemParameters) (a : ℝ) (j i : Fin p.n)
    (z : JointSpace 1 0) : JointSpace 1 0 :=
  p.L • z + if i=j then (p.n : ℝ) • tilt a else 0

theorem component_hasGradientAt (p : ProblemParameters) (a : ℝ) (j i : Fin p.n)
    (z : JointSpace 1 0) :
    HasGradientAt (component p a j i) (componentGradient p a j i z) z :=
  BaselineHilbert.hasGradientAt_value p.L _ z

theorem component_average (p : ProblemParameters) (a : ℝ) (j : Fin p.n)
    (z : JointSpace 1 0) :
    componentAverage (component p a j) z = BaselineHilbert.value p.L (tilt a) z := by
  have hn : (p.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.n_pos)
  have hi (i : Fin p.n) : component p a j i z =
      p.L / 2 * ‖z‖ ^ 2 + if i=j then (p.n : ℝ) * ⟪tilt a,z⟫_ℝ else 0 := by
    by_cases h : i=j <;> simp [component, BaselineHilbert.value, h, real_inner_smul_left] <;> ring
  simp only [componentAverage, hi, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, BaselineHilbert.value]
  field_simp [hn]
  <;> ring

theorem joint_value (p : ProblemParameters) (a : ℝ) (x : PrimalSpace 1) :
    BaselineHilbert.value p.L (tilt a) (jointPoint x 0) =
      BaselineHilbert.value p.L (a • direction) x := by
  simp [BaselineHilbert.value, tilt, jointPoint, WithLp.prod_inner_apply,
    WithLp.norm_toLp_fst]

theorem primal_value (p : ProblemParameters) (a : ℝ) (j : Fin p.n) (x : PrimalSpace 1) :
    primalObjective (dualDomain p) (component p a j) x =
      BaselineHilbert.value p.L (a • direction) x := by
  change sSup ((fun y ↦ componentAverage (component p a j) (jointPoint x y)) '' {0}) = _
  rw [image_singleton]
  simp only [csSup_singleton]
  rw [component_average, joint_value]

def model (p : ProblemParameters) (a : ℝ) (j : Fin p.n)
    (hgap : a ^ 2 / (2 * p.L) ≤ p.gap) : Problem p 1 0 (dualDomain p) where
  component := component p a j
  componentGradient := componentGradient p a j
  neighborhood := univ
  neighborhood_open := isOpen_univ
  domain_subset := subset_univ _
  gradient_correct := fun i z _ ↦ component_hasGradientAt p a j i z
  average_dual_concave := by
    intro x
    have hf : (fun y : DualSpace 0 ↦ componentAverage (component p a j) (jointPoint x y)) =
        fun _ ↦ componentAverage (component p a j) (jointPoint x 0) := by
      funext y
      rw [Subsingleton.elim y 0]
    rw [hf]
    exact concaveOn_const _ (dualDomain p).convex
  initialPoint := 0
  value_bddBelow := by
    have he : primalObjective (dualDomain p) (component p a j) =
        BaselineHilbert.value p.L (a • direction) := funext (primal_value p a j)
    rw [he]
    exact BaselineHilbert.bounded_below p.L_pos _
  initial_gap := by
    have he : primalObjective (dualDomain p) (component p a j) =
        BaselineHilbert.value p.L (a • direction) := funext (primal_value p a j)
    rw [he, BaselineHilbert.initial_gap p.L_pos]
    simpa only [norm_smul, Real.norm_eq_abs, direction_norm, mul_one, sq_abs] using hgap

theorem model_individualSmooth (p : ProblemParameters) (a : ℝ) (j : Fin p.n)
    (hgap : a ^ 2 / (2 * p.L) ≤ p.gap) : (model p a j hgap).individualSmooth := by
  intro i x hx y hy
  exact BaselineHilbert.gradient_lipschitz p.L_pos.le _ x y

theorem model_envelope (p : ProblemParameters) (a : ℝ) (j : Fin p.n)
    (hgap : a ^ 2 / (2 * p.L) ≤ p.gap) :
    problemMoreauEnvelope (model p a j hgap) =
      moreauEnvelope (BaselineHilbert.value p.L (a • direction)) p.L := by
  funext x
  unfold problemMoreauEnvelope moreauEnvelope
  congr 2
  funext y
  change primalObjective (dualDomain p) (component p a j) y + _ = _
  rw [primal_value]
  rfl

theorem stationary_norm (p : ProblemParameters) (a : ℝ) (j : Fin p.n)
    (hgap : a ^ 2 / (2 * p.L) ≤ p.gap) (x : PrimalSpace 1)
    (hs : StationaryOutput (model p a j hgap) x) :
    ‖gradient (moreauEnvelope (BaselineHilbert.value p.L (a • direction)) p.L) x‖ ≤ p.epsilon := by
  obtain ⟨g,hg,hgn⟩ := hs
  rw [model_envelope] at hg
  rw [hg.gradient]
  exact hgn

def baseOracle (p : ProblemParameters) (q : OracleQuery p.n 1 (dualDomain p)) : OracleAnswer 1 0 :=
  (BaselineHilbert.value p.L 0 (queryPoint q), (p.L • queryPoint q).fst,
    (p.L • queryPoint q).snd)

theorem oracle_agrees (p : ProblemParameters) (a : ℝ) (j : Fin p.n)
    (hgap : a ^ 2 / (2 * p.L) ≤ p.gap) (q : OracleQuery p.n 1 (dualDomain p))
    (hq : q.1 ≠ j) :
    oracleResponse (model p a j hgap) q = baseOracle p q := by
  simp [oracleResponse, model, component, componentGradient, hq, baseOracle]

end

end NCConcave16991.BaselineProblem
