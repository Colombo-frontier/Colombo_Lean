import NCConcave16991.Problem
import NCConcave16991.WeakConvexity
import NCConcave16991.MoreauEnvelope
import Mathlib.Analysis.Convex.Continuous

/-! # Analytic consequences of the actual finite-sum problem assumptions -/

open Set InnerProductSpace MeasureTheory
open scoped InnerProductSpace ENNReal

namespace NCConcave16991

noncomputable section

def primalInclusion (dx dy : ℕ) : PrimalSpace dx →L[ℝ] JointSpace dx dy :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (PrimalSpace dx) (DualSpace dy)).symm :
    (PrimalSpace dx × DualSpace dy) →L[ℝ] JointSpace dx dy).comp
      (ContinuousLinearMap.inl ℝ (PrimalSpace dx) (DualSpace dy))

theorem jointPoint_hasFDerivAt {dx dy : ℕ} (x : PrimalSpace dx) (y : DualSpace dy) :
    HasFDerivAt (fun u => jointPoint u y) (primalInclusion dx dy) x := by
  convert (primalInclusion dx dy).hasFDerivAt.add_const (jointPoint 0 y) using 1
  ext u
  change WithLp.toLp 2 (u, y) = WithLp.toLp 2 (u, 0) + WithLp.toLp 2 (0, y)
  simp [← WithLp.toLp_add]

namespace Problem

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- A primal section has the first coordinate of the actual averaged gradient. -/
theorem hasGradientAt_primal_section (P : Problem p dx dy K)
    (x : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    HasGradientAt (fun u => componentAverage P.component (jointPoint u y))
      (averageMap P.componentGradient (jointPoint x y)).fst x := by
  have hj := P.hasGradientAt_average (jointPoint x y) hy
  have hc := hj.hasFDerivAt.comp x (jointPoint_hasFDerivAt x y)
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin : toDual ℝ (PrimalSpace dx)
      (averageMap P.componentGradient (jointPoint x y)).fst =
      (toDual ℝ (JointSpace dx dy) (averageMap P.componentGradient (jointPoint x y))).comp
        (primalInclusion dx dy) := by
    ext u
    change ⟪(averageMap P.componentGradient (jointPoint x y)).fst, u⟫_ℝ =
      ⟪averageMap P.componentGradient (jointPoint x y), primalInclusion dx dy u⟫_ℝ
    simp [primalInclusion, WithLp.prod_inner_apply]
  rw [hlin]
  exact hc

theorem primal_section_gradient_lipschitz (P : Problem p dx dy K)
    (h : P.averagedSmooth) (y : DualSpace dy) (hy : y ∈ K.carrier)
    (x x' : PrimalSpace dx) :
    ‖(averageMap P.componentGradient (jointPoint x y)).fst -
        (averageMap P.componentGradient (jointPoint x' y)).fst‖ ≤ p.L * ‖x - x'‖ := by
  have hg := P.average_gradient_lipschitz h (jointPoint x y) hy (jointPoint x' y) hy
  have hj : ‖jointPoint x y - jointPoint x' y‖ = ‖x - x'‖ := by
    change ‖WithLp.toLp 2 (x - x', y - y)‖ = ‖x - x'‖
    rw [sub_self, WithLp.norm_toLp_fst]
  rw [hj] at hg
  apply le_trans _ hg
  simpa only [WithLp.sub_fst] using WithLp.norm_fst_le
    (p := 2) (α := PrimalSpace dx) (β := DualSpace dy)
    (averageMap P.componentGradient (jointPoint x y) -
      averageMap P.componentGradient (jointPoint x' y))

theorem primal_section_weaklyConvex (P : Problem p dx dy K)
    (h : P.averagedSmooth) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    WeaklyConvex p.L (fun x => componentAverage P.component (jointPoint x y)) :=
  weaklyConvex_of_lipschitz_gradient p.L_pos.le
    (fun x => P.hasGradientAt_primal_section x y hy)
    (P.primal_section_gradient_lipschitz h y hy)

/-- Section 2 / Appendix A.1: AS makes the actual maximized value L-weakly convex. -/
theorem primal_weaklyConvex (P : Problem p dx dy K) (h : P.averagedSmooth) :
    WeaklyConvex p.L (primalObjective K P.component) := by
  letI : Nonempty K.carrier := K.nonempty.to_subtype
  have hb (x : PrimalSpace dx) :
      BddAbove (range (fun y : K.carrier => componentAverage P.component (jointPoint x y))) := by
    obtain ⟨y, hy, hmax⟩ := K.compact.exists_isMaxOn K.nonempty (P.average_dual_continuous x)
    refine ⟨componentAverage P.component (jointPoint x y), ?_⟩
    rintro v ⟨y', rfl⟩
    exact hmax y'.property
  have hw := weaklyConvex_sSup
    (fun y : K.carrier => P.primal_section_weaklyConvex h y y.property) hb
  have he : primalObjective K P.component = (fun x =>
      sSup (range (fun y : K.carrier => componentAverage P.component (jointPoint x y)))) := by
    funext x
    unfold primalObjective
    rw [image_eq_range]
  rw [he]
  exact hw

/-- A finite-valued weakly convex function on the finite-dimensional primal
space is continuous, so Moreau minimizers exist without an extra assumption. -/
theorem primal_continuous (P : Problem p dx dy K) (h : P.averagedSmooth) :
    Continuous (primalObjective K P.component) := by
  have hw := P.primal_weaklyConvex h
  have hc : Continuous (fun x : PrimalSpace dx =>
      primalObjective K P.component x + p.L / 2 * ‖x‖ ^ 2) :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hw)
  have hq : Continuous (fun x : PrimalSpace dx => p.L / 2 * ‖x‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  convert hc.sub hq using 1
  ext x
  dsimp
  ring

theorem problemMoreauEnvelope_eq (P : Problem p dx dy K) :
    problemMoreauEnvelope P = moreauEnvelope (primalObjective K P.component) p.L := rfl

/-- The actual infimum-defined problem envelope has the paper's derivative. -/
theorem moreau_hasGradientAt (P : Problem p dx dy K) (h : P.averagedSmooth)
    (c : PrimalSpace dx) :
    HasGradientAt (problemMoreauEnvelope P)
      ((2 * p.L) • (c - proximalMap p.L_pos (P.primal_continuous h) P.value_bddBelow c)) c := by
  rw [P.problemMoreauEnvelope_eq]
  exact moreauEnvelope_gradient_formula p.L_pos (P.primal_continuous h)
    P.value_bddBelow (P.primal_weaklyConvex h) c

theorem proximalMap_continuous (P : Problem p dx dy K) (h : P.averagedSmooth) :
    Continuous (proximalMap p.L_pos (P.primal_continuous h) P.value_bddBelow) := by
  have hlip : LipschitzWith 2
      (proximalMap p.L_pos (P.primal_continuous h) P.value_bddBelow) := by
    apply LipschitzWith.of_dist_le_mul
    intro c d
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using
      proxPoint_lipschitz p.L_pos (P.primal_weaklyConvex h)
        (proximalMap_spec p.L_pos (P.primal_continuous h) P.value_bddBelow c)
        (proximalMap_spec p.L_pos (P.primal_continuous h) P.value_bddBelow d)
  exact hlip.continuous

/-- The actual Moreau gradient is continuous, giving Borel stationarity events. -/
theorem moreau_gradient_continuous (P : Problem p dx dy K) (h : P.averagedSmooth) :
    Continuous (gradient (problemMoreauEnvelope P)) := by
  have he : gradient (problemMoreauEnvelope P) = (fun c =>
      (2 * p.L) • (c - proximalMap p.L_pos (P.primal_continuous h) P.value_bddBelow c)) :=
    funext (fun c => (P.moreau_hasGradientAt h c).gradient)
  rw [he]
  exact (continuous_const : Continuous (fun _ : PrimalSpace dx ↦ (2 * p.L : ℝ))).smul
    (continuous_id.sub (P.proximalMap_continuous h))

/-- The model's derivative-based success event agrees exactly with the paper's
gradient-norm event; the derivative existence is established above. -/
theorem stationaryOutput_iff (P : Problem p dx dy K) (h : P.averagedSmooth)
    (c : PrimalSpace dx) :
    StationaryOutput P c ↔ ‖gradient (problemMoreauEnvelope P) c‖ ≤ p.epsilon := by
  constructor
  · rintro ⟨g, hg, hn⟩
    rwa [hg.gradient]
  · intro hn
    have hg := P.moreau_hasGradientAt h c
    refine ⟨_, hg, ?_⟩
    rwa [hg.gradient] at hn

/-- The initial Moreau-gradient estimate stated after Theorem 3.3. -/
theorem initial_moreau_gradient_sq (P : Problem p dx dy K) (h : P.averagedSmooth) :
    ‖gradient (problemMoreauEnvelope P) P.initialPoint‖ ^ 2 ≤ 4 * p.L * p.gap := by
  rw [P.problemMoreauEnvelope_eq]
  exact moreauEnvelope_initial_gradient_sq p.L_pos (P.primal_continuous h)
    P.value_bddBelow (P.primal_weaklyConvex h) P.initial_gap

theorem initial_stationary_of_small_accuracy (P : Problem p dx dy K)
    (h : P.averagedSmooth) (hsmall : p.L * p.gap / p.epsilon ^ 2 ≤ 1 / 4) :
    StationaryOutput P P.initialPoint := by
  apply (P.stationaryOutput_iff h P.initialPoint).2
  have hscale := (div_le_iff₀ (sq_pos_of_pos p.epsilon_pos)).mp hsmall
  have hg := P.initial_moreau_gradient_sq h
  nlinarith [norm_nonneg (gradient (problemMoreauEnvelope P) P.initialPoint), p.epsilon_pos]

end Problem

/-- The constant policy is genuinely admissible and makes no component calls.
This proves the trivial-accuracy statement in the actual randomized oracle model. -/
theorem validBudget_zero_of_small_accuracy (p : ProblemParameters)
    (hsmall : p.L * p.gap / p.epsilon ^ 2 ≤ 1 / 4) :
    ValidBudget p .averaged 0 := by
  intro dx dy K x0
  let A : RandomizedPolicy K (n := p.n) (dx := dx) := {
    Seed := Unit
    seedSpace := inferInstance
    law := Measure.dirac ()
    law_probability := inferInstance
    policy := {
      next := fun _ _ => Sum.inl x0
      final := fun _ _ => x0
      next_measurable := measurable_const
      final_measurable := measurable_const } }
  refine ⟨A, ?_⟩
  intro P h0 hP
  have hs : StationaryOutput P x0 := by
    rw [← h0]
    exact P.initial_stationary_of_small_accuracy hP hsmall
  have he : {seed : Unit | StationaryOutput P x0} = Set.univ := by
    ext seed
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact hs
  change MeasurableSet {seed : Unit | StationaryOutput P x0} ∧
    (2 / 3 : ℝ≥0∞) ≤ Measure.dirac () {seed : Unit | StationaryOutput P x0}
  rw [he]
  constructor
  · exact MeasurableSet.univ
  · apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num

theorem validBudget_zero_individual_of_small_accuracy (p : ProblemParameters)
    (hsmall : p.L * p.gap / p.epsilon ^ 2 ≤ 1 / 4) :
    ValidBudget p .individual 0 :=
  validBudget_individual_of_averaged (validBudget_zero_of_small_accuracy p hsmall)

end

end NCConcave16991
