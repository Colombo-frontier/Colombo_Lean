import Bilevel.PolishedHistoryQuerySource
import Bilevel.PolishedSourcePostCurvatureUpper

/-! The source-facing model conditions only on the actual query and past
observations; no unused private seed or entire private state is inserted
into its filtration. For our PUBLIC query body, full-state adaptedness is
proved from its actual recursion, enabling the already certified upper bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful OracleCode CachedBudgetCalibration
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg ε : ℝ}
variable {M : SourceMean G μ L ρ Δ R₀} {A : Algorithm G}

theorem QuerySourceExecution.public_state_information
    (E : QuerySourceExecution M A σf σg) (s₀ : A.State) (hstart : ∀ p,A.start p=s₀)
    (n : ℕ) : Measurable[E.information n] (E.state n) := by
  induction n with
  | zero =>
    have he : E.state 0=fun _ => s₀ := funext (fun ω => (E.init ω).trans (hstart _))
    rw [he]
    exact measurable_const
  | succ n ih =>
    have hs : Measurable[E.information (n+1)] (E.state n) :=
      ih.mono (E.information_mono (Nat.le_succ n)) le_rfl
    have he : E.state (n+1)=fun ω => if A.program.halt (E.state n ω)=true
        then E.state n ω else A.program.update (E.state n ω,E.obs n ω) := funext (E.next n)
    rw [he]
    exact hs.ite ((A.program.halt_measurable.comp hs) (measurableSet_singleton true))
      (A.program.update_measurable.comp (hs.prodMk (E.obs_information n)))

/-- For a public body the stronger internal interface follows from the
weaker source conditions. Unused private randomness is never conditioned on. -/
def QuerySourceExecution.publicStrong [Subsingleton A.Private]
    (E : QuerySourceExecution M A σf σg) (s₀ : A.State) (hstart : ∀ p,A.start p=s₀) :
    SourceRandomExecution M A σf σg where
  Ω:=E.Ω
  law:=E.law
  privateSeed:=E.privateSeed
  private_measurable:=E.private_measurable
  private_law:=E.private_law
  state:=E.state
  obs:=E.obs
  sample:=E.sample
  sample_measurable:=E.sample_measurable
  obs_eq:=E.obs_eq
  state_measurable:=E.state_measurable
  obs_measurable:=E.obs_measurable
  init:=Filter.Eventually.of_forall E.init
  next:=fun n => Filter.Eventually.of_forall (E.next n)
  information:=E.information
  information_le:=E.information_le
  information_mono:=E.information_mono
  obs_information:=E.obs_information
  private_information:=fun n => @measurable_of_subsingleton_codomain E.Ω A.Private
    (E.information n) A.measurablePrivate inferInstance E.privateSeed
  state_information:=E.public_state_information s₀ hstart
  upper_square_integrable:=E.upper_square_integrable
  lower_square_integrable:=E.lower_square_integrable
  upper_mean:=E.upper_mean
  lower_mean:=E.lower_mean
  upper_variance:=E.upper_variance
  lower_variance:=E.lower_variance

namespace SourceMean
variable (M : SourceMean G μ L ρ Δ R₀)

theorem query_source_frozen_normalized_upper
    (E : QuerySourceExecution M
      (sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg M.x₀ M.yinit).bodyAsAlgorithm σf σg)
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    E.postRisk≤ENNReal.ofReal ε ∧
    E.cost≤ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  let A := sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg M.x₀ M.yinit
  have hs : ∀ p : A.Private,A.bodyAsAlgorithm.start p=A.start () := by
    intro p
    cases p
    rfl
  letI : Subsingleton A.bodyAsAlgorithm.Private := by
    change Subsingleton Unit
    infer_instance
  let E' := E.publicStrong (A.start ()) hs
  simpa only [QuerySourceExecution.postRisk,QuerySourceExecution.postOutput,QuerySourceExecution.cost,
    QuerySourceExecution.path,SourceRandomExecution.postRisk,SourceRandomExecution.postOutput,
    SourceRandomExecution.cost,SourceRandomExecution.path,QuerySourceExecution.publicStrong] using
      M.source_frozen_post_upper E' hL hΔ hε hκ

theorem query_source_frozen_curvature_upper {Λcert CF : ℝ}
    (E : QuerySourceExecution M
      (sourcePrescribedPostAlgorithm G μ L ρ σf σg
        (CachedUpper.controlledCurvature L μ L L Λcert) Δ ε R₀ M.x₀ M.yinit).bodyAsAlgorithm σf σg)
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hκ : 1≤L/μ) (hθ : 1≤ρ/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤CF*L*(L/μ)^2) (hlip : M.CurvatureBound Λcert) :
    E.postRisk≤ENNReal.ofReal ε ∧
    E.cost≤ENNReal.ofReal (CachedUpper.controlledThreeRateBound L μ L L L ρ σf σg
      (CachedUpper.controlledCurvature L μ L L Λcert) (CachedUpper.controlledConstant CF) Δ ε R₀) := by
  let A := sourcePrescribedPostAlgorithm G μ L ρ σf σg
    (CachedUpper.controlledCurvature L μ L L Λcert) Δ ε R₀ M.x₀ M.yinit
  have hs : ∀ p : A.Private,A.bodyAsAlgorithm.start p=A.start () := by
    intro p
    cases p
    rfl
  letI : Subsingleton A.bodyAsAlgorithm.Private := by
    change Subsingleton Unit
    infer_instance
  let E' := E.publicStrong (A.start ()) hs
  simpa only [QuerySourceExecution.postRisk,QuerySourceExecution.postOutput,QuerySourceExecution.cost,
    QuerySourceExecution.path,SourceRandomExecution.postRisk,SourceRandomExecution.postOutput,
    SourceRandomExecution.cost,SourceRandomExecution.path,QuerySourceExecution.publicStrong] using
      M.source_frozen_controlled_post_upper E' hL hΔ hε hκ hθ haccuracy hcert hlip

end SourceMean

/-- The solver principle uses actual cost and risk in the weak-information
source model; no comparison with a stronger minimax definition is assumed. -/
theorem query_post_complexity_le_of_solver (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) (ε : ℝ) (A : PostSolverAt) (b : ℝ≥0∞)
    (hrisk : queryPostAccurate (σf:=σf) (σg:=σg) C conservative ε A)
    (hcost : ∀ K : QueryPostChallenge A μ L ρ Δ R₀ σf σg,
      C K.geometry K.mean → (conservative=true → K.execution.IsConservative) → K.execution.cost≤b) :
    queryPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤b := by
  unfold queryPostComplexity
  apply iInf_le_of_le ⟨A,hrisk⟩
  apply iSup_le
  intro K
  exact hcost K.val K.property.1 K.property.2

theorem query_source_normalized_complexity_upper (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) {ε : ℝ} (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    queryPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤
      ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  apply query_post_complexity_le_of_solver C conservative ε
    (fun G x y => sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg x y)
  · intro K _ _
    exact (K.mean.query_source_frozen_normalized_upper K.execution hL hΔ hε hκ).1
  · intro K _ _
    exact (K.mean.query_source_frozen_normalized_upper K.execution hL hΔ hε hκ).2

theorem query_source_three_term_complexity_upper (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) {ε : ℝ} (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε)
    (hθ : 1≤ρ/μ) (hκ : 1≤L/μ) (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    queryPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤
      ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) :=
  (query_source_normalized_complexity_upper C conservative hL hΔ.le hε hκ).trans
    (ENNReal.ofReal_le_ofReal (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))

theorem query_source_curvature_complexity_upper (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) {Λcert CF : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hκ : 1≤L/μ) (hθ : 1≤ρ/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤CF*L*(L/μ)^2) (hC : ∀ G M,C G M → M.CurvatureBound Λcert) :
    queryPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤
      ENNReal.ofReal (CachedUpper.controlledThreeRateBound L μ L L L ρ σf σg
        (CachedUpper.controlledCurvature L μ L L Λcert) (CachedUpper.controlledConstant CF) Δ ε R₀) := by
  apply query_post_complexity_le_of_solver C conservative ε
    (fun G x y => sourcePrescribedPostAlgorithm G μ L ρ σf σg
      (CachedUpper.controlledCurvature L μ L L Λcert) Δ ε R₀ x y)
  · intro K hK _
    exact (K.mean.query_source_frozen_curvature_upper K.execution hL hΔ hε hκ hθ haccuracy hcert
      (hC K.geometry K.mean hK)).1
  · intro K hK _
    exact (K.mean.query_source_frozen_curvature_upper K.execution hL hΔ hε hκ hθ haccuracy hcert
      (hC K.geometry K.mean hK)).2

end Bilevel.PolishedHistory
