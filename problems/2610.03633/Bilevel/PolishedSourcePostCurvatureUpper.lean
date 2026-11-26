import Bilevel.PolishedSourcePostClasses
import Bilevel.CachedCurvatureUpper

/-! Supplied hyperobjective curvature in the same actual source minimax
model, with the literal public dispatch and post-query independent choice. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful OracleCode CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg ε : ℝ}

def sourcePrescribedPostAlgorithm (G : Geometry) (μ L ρ σf σg Λ Δ ε R₀ : ℝ)
    (x₀ : G.X) (yinit : G.Y) : PostAlgorithm G := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := sourceFrozenDispatchMachine G μ L L L ρ σf σg Λ Δ ε R₀ x₀ yinit
  exact {
    Private:=Unit
    State:=m.state
    Output:=CachedOuterProcedure.State G.X G.Y
    Terminal:=Fin (outerCount Λ Δ ε)
    privateLaw:=Measure.dirac ()
    body:=m.program
    start:=m.start
    start_measurable:=m.start_measurable
    terminalLaw:=StochasticOuter.uniformLaw (outerCount Λ Δ ε)
    select:=sourceFrozenDispatchSelect Λ Δ ε x₀
    select_measurable:=by
      classical
      unfold sourceFrozenDispatchSelect
      split_ifs
      · exact measurable_const
      · exact CachedOracleCode.selected_measurable Λ Δ ε x₀ }

namespace SourceMean
variable (M : SourceMean G μ L ρ Δ R₀)

theorem source_frozen_prescribed_post_upper {Λ : ℝ}
    (E : SourceRandomExecution M
      (sourcePrescribedPostAlgorithm G μ L ρ σf σg Λ Δ ε R₀ M.x₀ M.yinit).bodyAsAlgorithm σf σg)
    (hΛ : 0<Λ) (hLaΛ : anchorSmoothness L (L/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (hlip : M.CurvatureBound Λ) :
    E.postRisk≤ENNReal.ofReal ε ∧
    E.cost≤ENNReal.ofReal (CachedUpper.rateBound μ L L L ρ σf σg Λ Δ ε R₀) := by
  let m := sourceFrozenDispatchMachine G μ L L L ρ σf σg Λ Δ ε R₀ M.x₀ M.yinit
  let A := sourcePrescribedPostAlgorithm G μ L ρ σf σg Λ Δ ε R₀ M.x₀ M.yinit
  have hs : ∀ p : A.Private,A.start p=m.start () := by
    intro p
    cases p
    rfl
  let E' := E.publicExperiment (m.start ()) hs
  have hfull (x y : G.X) :
      ‖gradient (M.primitive.hyperobjective M.primitive.canonicalResponse) x-
        gradient (M.primitive.hyperobjective M.primitive.canonicalResponse) y‖≤Λ*‖x-y‖ := by
    rw [M.canonical_hyperobjective_eq]
    exact hlip x y
  have hlower (x : G.X) : M.gap.floor≤M.primitive.hyperobjective M.primitive.canonicalResponse x := by
    rw [M.canonical_hyperobjective_eq]
    exact M.gap.lower_bound x
  have hgap : M.primitive.hyperobjective M.primitive.canonicalResponse M.x₀-M.gap.floor≤Δ := by
    rw [M.canonical_hyperobjective_eq]
    exact M.gap.gap
  have hinit : ‖M.yinit-M.primitive.canonicalResponse.y M.x₀‖≤R₀ := by
    rw [M.canonical_response_eq]
    exact M.initialization
  have hc := source_frozen_general_dispatch_upper M.primitive M.x₀ M.yinit M.gap.floor E'
    rfl hΛ hLaΛ hΔ hε hfull hlower hgap hinit
  exact ⟨by simpa only [SourceRandomExecution.postRisk,SourceRandomExecution.postOutput,M.loss_eq_canonical]
    using hc.1,hc.2.1⟩

theorem source_frozen_controlled_post_upper {Λcert CF : ℝ}
    (E : SourceRandomExecution M
      (sourcePrescribedPostAlgorithm G μ L ρ σf σg
        (CachedUpper.controlledCurvature L μ L L Λcert) Δ ε R₀ M.x₀ M.yinit).bodyAsAlgorithm σf σg)
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hκ : 1≤L/μ) (hθ : 1≤ρ/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤CF*L*(L/μ)^2) (hlip : M.CurvatureBound Λcert) :
    E.postRisk≤ENNReal.ofReal ε ∧
    E.cost≤ENNReal.ofReal (CachedUpper.controlledThreeRateBound L μ L L L ρ σf σg
      (CachedUpper.controlledCurvature L μ L L Λcert) (CachedUpper.controlledConstant CF) Δ ε R₀) := by
  let Λ := CachedUpper.controlledCurvature L μ L L Λcert
  have hΛ : 0<Λ := hL.trans_le (le_max_left _ _)
  have hLaΛ : anchorSmoothness L (L/μ)≤Λ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hcertΛ : Λcert≤Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hfull : M.CurvatureBound Λ := fun x y =>
    (hlip x y).trans (mul_le_mul_of_nonneg_right hcertΛ (norm_nonneg _))
  have hparameters := CachedNormalizedRate.normalized_parameters M.primitive.μ_pos hL
    M.primitive.Lf_nonneg M.primitive.Lg_nonneg M.primitive.Cf_nonneg
    le_rfl le_rfl le_rfl (div_nonneg M.primitive.ρ_nonneg M.primitive.μ_pos.le) hκ
  have hΛb : Λ≤CachedUpper.controlledConstant CF*L*(L/μ)^2 :=
    CachedUpper.controlled_curvature_budget hL.le hκ hcert hparameters.2.1
  have hc := M.source_frozen_prescribed_post_upper E hΛ hLaΛ hΔ.le hε hfull
  have hcontrolled := CachedUpper.rateBound_le_curvatureControlled (σf:=σf) (σg:=σg) (R₀:=R₀)
    M.primitive.μ_pos hL M.primitive.Lf_nonneg M.primitive.Lg_nonneg M.primitive.Cf_nonneg
    M.primitive.ρ_nonneg le_rfl le_rfl le_rfl hθ hκ hΔ hε haccuracy hΛb
  exact ⟨hc.1,hc.2.trans (ENNReal.ofReal_le_ofReal hcontrolled)⟩

end SourceMean

/-- Any mean subclass satisfying the prescribed curvature condition has
the same source-class upper witness. This also covers positive dimensions. -/
theorem source_post_curvature_complexity_upper (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) {Λcert CF : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hκ : 1≤L/μ) (hθ : 1≤ρ/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤CF*L*(L/μ)^2) (hC : ∀ G M,C G M → M.CurvatureBound Λcert) :
    restrictedPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤
      ENNReal.ofReal (CachedUpper.controlledThreeRateBound L μ L L L ρ σf σg
        (CachedUpper.controlledCurvature L μ L L Λcert) (CachedUpper.controlledConstant CF) Δ ε R₀) := by
  apply restricted_post_complexity_le_of_solver C conservative ε
    (fun G x y => sourcePrescribedPostAlgorithm G μ L ρ σf σg
      (CachedUpper.controlledCurvature L μ L L Λcert) Δ ε R₀ x y)
  · intro K hK _
    exact (K.mean.source_frozen_controlled_post_upper K.execution hL hΔ hε hκ hθ haccuracy hcert
      (hC K.geometry K.mean hK)).1
  · intro K hK _
    exact (K.mean.source_frozen_controlled_post_upper K.execution hL hΔ hε hκ hθ haccuracy hcert
      (hC K.geometry K.mean hK)).2

end Bilevel.PolishedHistory
