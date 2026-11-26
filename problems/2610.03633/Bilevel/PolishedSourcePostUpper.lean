import Bilevel.PolishedHistorySourcePost
import Bilevel.PolishedHistorySourceDispatch
import Bilevel.PolishedHistorySourceFiltration

/-! The actual source class uses an arbitrary randomized query body and an
independent terminal draw. A public deterministic query body is an actual
SourceExperiment, with its adapted call clock derived from the filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful OracleCode CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg ε : ℝ}
variable {M : SourceMean G μ L ρ Δ R₀} {A : PostAlgorithm G}

/-- Coordinate decoding and a public start preserve the actual paired
conditional experiment. No kernel representation is an input. -/
def SourceRandomExecution.publicExperiment
    (E : SourceRandomExecution M A.bodyAsAlgorithm σf σg)
    (s₀ : A.State) (hstart : ∀ p,A.start p=s₀) :
    SourceExperiment A.body (generalPrimitiveUpper M.primitive) (generalPrimitiveLower M.primitive)
      (rawReadUpper G) (rawReadLower G) σf σg where
  Ω:=E.Ω
  law:=E.law
  state:=E.state
  obs:=fun n ω => splitResponse (E.obs n ω)
  state_measurable:=E.state_measurable
  obs_measurable:=fun n => splitResponse_measurable.comp (E.obs_measurable n)
  initial:=s₀
  init:=by
    filter_upwards [E.init] with ω hω
    exact hω.trans (hstart _)
  next:=E.next
  information:=E.information
  information_le:=E.information_le
  state_information:=clockedState_information A.body E.state E.information
    E.information_mono E.state_information
  upper_square_integrable:=E.upper_square_integrable
  lower_square_integrable:=E.lower_square_integrable
  upper_mean:=E.upper_mean
  lower_mean:=E.lower_mean
  upper_variance:=E.upper_variance
  lower_variance:=E.lower_variance

theorem SourceRandomExecution.publicExperiment_cost
    (E : SourceRandomExecution M A.bodyAsAlgorithm σf σg)
    (s₀ : A.State) (hstart : ∀ p,A.start p=s₀) :
    (E.publicExperiment s₀ hstart).actualCost=E.cost := rfl

/-- Literal public dispatch and cached body, with the uniform index sampled
only after querying. All code inputs are public budgets and initial points. -/
def sourceFrozenPostAlgorithm (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ)
    (x₀ : G.X) (yinit : G.Y) : PostAlgorithm G := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
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

theorem canonical_response_eq (x : G.X) : M.primitive.canonicalResponse.y x=M.response.y x :=
  M.primitive.lower_solution_unique x _ _ (M.primitive.canonicalResponse.minimizes x) (M.response.minimizes x)

theorem canonical_hyperobjective_eq :
    M.primitive.hyperobjective M.primitive.canonicalResponse=M.primitive.hyperobjective M.response := by
  funext x
  unfold Model.Primitive.hyperobjective
  rw [M.canonical_response_eq]

theorem loss_eq_canonical (x : G.X) :
    M.loss x=‖gradient (M.primitive.hyperobjective M.primitive.canonicalResponse) x‖ := by
  rw [M.canonical_hyperobjective_eq]
  rfl

/-- The concrete public post-selector algorithm is uniformly correct for
every actual admissible conditional-moment execution in the source class. -/
theorem source_frozen_post_upper
    (E : SourceRandomExecution M
      (sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg M.x₀ M.yinit).bodyAsAlgorithm σf σg)
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    E.postRisk≤ENNReal.ofReal ε ∧
    E.cost≤ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  let m := sourceFrozenDispatchMachine G μ L L L ρ σf σg Λ Δ ε R₀ M.x₀ M.yinit
  let A := sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg M.x₀ M.yinit
  have hs : ∀ p : A.Private,A.start p=m.start () := by
    intro p
    cases p
    rfl
  let E' := E.publicExperiment (m.start ()) hs
  have hΛ : 0<Λ := hL.trans_le (le_max_left _ _)
  have hcurv : (1+L/μ)^2*(L+ρ*L/μ)≤Λ := le_max_right _ _
  have hLaΛ : anchorSmoothness L (L/μ)≤Λ := by
    have hh : 0≤(1+L/μ)^2*(ρ*L/μ) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg M.primitive.ρ_nonneg M.primitive.Cf_nonneg) M.primitive.μ_pos.le)
    unfold anchorSmoothness
    nlinarith
  have hlip (x y : G.X) : ‖gradient (M.primitive.hyperobjective M.primitive.canonicalResponse) x-
      gradient (M.primitive.hyperobjective M.primitive.canonicalResponse) y‖≤Λ*‖x-y‖ :=
    (M.primitive.gradient_hyperobjective_norm_sub_le M.primitive.canonicalResponse x y).trans
      (mul_le_mul_of_nonneg_right hcurv (norm_nonneg _))
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
    rfl hΛ hLaΛ hΔ hε hlip hlower hgap hinit
  have hnorm := CachedUpper.rateBound_le_normalized (σf:=σf) (σg:=σg) (ε:=ε) (R₀:=R₀)
    M.primitive.μ_pos hL M.primitive.Lf_nonneg M.primitive.Lg_nonneg M.primitive.Cf_nonneg
    M.primitive.ρ_nonneg le_rfl le_rfl le_rfl hκ hΔ
  constructor
  · simpa only [SourceRandomExecution.postRisk,SourceRandomExecution.postOutput,M.loss_eq_canonical]
      using hc.1
  · exact hc.2.1.trans (ENNReal.ofReal_le_ofReal hnorm)

end SourceMean

/-- Both oracle classes use one actual source minimax value and the same
public literal upper solver, including independent terminal selection. -/
theorem source_post_normalized_complexity_upper (conservative : Bool)
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    postSourceComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε≤
      ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  let A : PostSolverAt := fun G x y => sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg x y
  have hacc : postSourceAccurate (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε A := by
    intro C _
    exact (C.mean.source_frozen_post_upper C.execution hL hΔ hε hκ).1
  unfold postSourceComplexity
  apply iInf_le_of_le ⟨A,hacc⟩
  apply iSup_le
  intro C
  exact (C.val.mean.source_frozen_post_upper C.val.execution hL hΔ hε hκ).2

end Bilevel.PolishedHistory
