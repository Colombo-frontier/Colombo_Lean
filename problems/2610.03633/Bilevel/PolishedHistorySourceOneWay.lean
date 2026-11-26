import Bilevel.PolishedHistoryFreshSourceRun
import Bilevel.PolishedHistorySourceFrozenGeneral
import Bilevel.PolishedHistoryComparison

/-! One-way source-model certificates. The lower comparison needs only an
embedding of the actual admissible stationary fresh experiments, preserving
their costs and finite-cost stopped risks. No equivalence of oracle classes
or assumed final complexity inequality is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {μ L ρ Δ R₀ σf σg : ℝ}

/-- A purely semantic one-way embedding of the legal hard subclass into a
source experiment model. The fields identify executions, not rate bounds. -/
structure FreshSourceEmbedding (J : Type*) (cost risk : SolverAt → J → ℝ≥0∞) where
  challenge : ∀ (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg),I.IsConservative → J
  cost_eq : ∀ (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (hI : I.IsConservative) (A : SolverAt),
    cost A (challenge G I hI)=I.cost (A G 0 0)
  risk_eq : ∀ (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (hI : I.IsConservative) (A : SolverAt),
    cost A (challenge G I hI)≠⊤ → risk A (challenge G I hI)=I.risk (A G 0 0)

def sourceAccurate {J : Type*} (risk : SolverAt → J → ℝ≥0∞) (ε : ℝ) (A : SolverAt) : Prop :=
  ∀ j,risk A j≤ENNReal.ofReal ε

/-- Restriction to the actual fresh subclass is the only minimax order
needed for the source lower bound. Infinite costs are handled first. -/
theorem fresh_source_minimax_order {J : Type*} (cost risk : SolverAt → J → ℝ≥0∞)
    (e : FreshSourceEmbedding (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) J cost risk) (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
      ChiMinimax.complexity cost (sourceAccurate risk ε) := by
  unfold PrimitiveQuery.Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  let T : ℝ≥0∞ := ⨆ j,cost A.val j
  by_cases hT : T=⊤
  · change _≤T
    rw [hT]
    exact le_top
  have hb (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (hI : I.IsConservative) :
      cost A.val (e.challenge G I hI)≤T := le_iSup (fun j => cost A.val j) _
  have hf (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (hI : I.IsConservative) :
      cost A.val (e.challenge G I hI)≠⊤ := by
    intro htop
    exact hT (top_le_iff.mp (by rw [← htop];exact hb G I hI))
  let oldSolver : PrimitiveQuery.Solver := fun G => A.val G 0 0
  have hacc : PrimitiveQuery.Accurate (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε oldSolver := by
    intro G I hI
    have hh := A.property (e.challenge G I hI)
    rw [e.risk_eq G I hI A.val (hf G I hI)] at hh
    exact hh
  refine (iInf_le _ ⟨oldSolver,hacc⟩).trans ?_
  apply iSup_le
  intro I
  have hh := hb I.val.1 I.val.2 I.property
  rw [e.cost_eq] at hh
  exact hh

/-- The existing history execution is a concrete semantic instance of the
one-way embedding, preserving the original program and paired response. -/
def stationaryHistorySourceEmbedding :
    FreshSourceEmbedding (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
      {I : (G : Geometry) × Instance G μ L ρ Δ R₀ σf σg // I.2.IsConservative}
      (fun A I => I.val.2.cost (A I.val.1 I.val.2.x₀ I.val.2.yinit))
      (fun A I => I.val.2.risk (A I.val.1 I.val.2.x₀ I.val.2.yinit)) where
  challenge G I hI:=⟨⟨G,ofStationary I⟩,ofStationary_isConservative I hI⟩
  cost_eq G I _ A:=ofStationary_cost I (A G 0 0)
  risk_eq G I _ A hc:=ofStationary_risk_of_cost_finite I (A G 0 0) hc

/-- Uniform source lower bound for every semantic source model containing
these actual stationary conditional experiments. The only model premises
are exact execution-cost and stopped-risk identification. -/
theorem uniform_source_one_way_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      ∀ (J : Type*) (cost risk : SolverAt → J → ℝ≥0∞),
      FreshSourceEmbedding (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) J cost risk →
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        ChiMinimax.complexity cost (sourceAccurate risk ε) := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hl⟩ := ChiUniformLower.uniform_both_classes_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc J cost risk e
  exact (hl L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc).1.trans
    (fresh_source_minimax_order cost risk e ε)

/-- No moment or execution-admissibility premise remains for the actual
fresh subclass: it works for arbitrary private random starts and stopping
programs, and retains exact original-call costs. -/
theorem stationary_source_one_way_certificate
    {G : Geometry} (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (A : Algorithm G) :
    ConditionalFreshRunCertificate I A ∧
      (ofStationary I).cost A=I.cost A ∧
      ((ofStationary I).cost A≠⊤ → (ofStationary I).risk A=I.risk A) ∧
      (I.IsConservative → (ofStationary I).IsConservative) :=
  ⟨stationary_actual_source_admissible I A,ofStationary_cost I A,
    ofStationary_risk_of_cost_finite I A,ofStationary_isConservative I⟩

/-- Accuracy tested on the genuine conditional source fresh experiments,
using their actual stopped source paths. -/
def sourceFreshAccurate (ε : ℝ) (A : PrimitiveQuery.Solver) : Prop :=
  ∀ (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg),I.IsConservative →
    freshSourceRisk I (A G)≤ENNReal.ofReal ε

def sourceFreshWorstCost (A : PrimitiveQuery.Solver) : ℝ≥0∞ :=
  ⨆ I : {I : (G : Geometry) × PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg // I.2.IsConservative},
    freshSourceCost I.val.2 (A I.val.1)

/-- The lower source certificate applies to every randomized algorithm:
its oracle legality, original calls and output loss all concern the same
actual private-seed/stream experiment. -/
theorem uniform_actual_source_solver_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      ∀ A : PrimitiveQuery.Solver,
      sourceFreshAccurate (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) ε A →
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        sourceFreshWorstCost (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) A := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hl⟩ := ChiUniformLower.uniform_both_classes_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc A hA
  have h := (hl L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc).1
  have hacc' : PrimitiveQuery.Accurate (PrimitiveQuery.conservativeClass (μ:=L/κ) (L:=L)
      (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε A := by
    intro G I hI
    rw [← freshSourceRisk_eq I (A G)]
    exact hA G I hI
  apply h.trans
  unfold PrimitiveQuery.Complexity ChiMinimax.complexity
  apply (iInf_le _ ⟨A,hacc'⟩).trans
  apply iSup_le
  intro I
  change I.val.2.cost (A I.val.1)≤sourceFreshWorstCost A
  rw [← freshSourceCost_eq I.val.2 (A I.val.1)]
  exact le_iSup (fun I : {I : (G : Geometry) × PrimitiveQuery.Instance G (L/κ) L (θ*(L/κ)) Δ R₀ σf σg // I.2.IsConservative} =>
    freshSourceCost I.val.2 (A I.val.1)) I

theorem actual_source_admissibility_and_metrics
    {G : Geometry} (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (A : Algorithm G) :
    ConditionalFreshRunCertificate I A ∧ freshSourceCost I A=I.cost A ∧ freshSourceRisk I A=I.risk A :=
  ⟨stationary_actual_source_admissible I A,freshSourceCost_eq I A,freshSourceRisk_eq I A⟩

section GeneralSource
open PrimitiveGeometry Stateful OracleCode CachedBudgetCalibration CachedParameterChoice
variable {G : Geometry} {Lf Lg Cf Λ ε : ℝ}

/-- The exact all-source conditional-experiment upper certificate, with
the same literal body and independent terminal random selection. -/
theorem source_general_upper_certificate
    (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ Lf Lg Cf ρ)
    (x₀ : G.X) (yinit : G.Y) (lower : ℝ)
    (E : SourceExperiment (sourceFrozenGeneralMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit).program
      (generalPrimitiveUpper P) (generalPrimitiveLower P) (rawReadUpper G) (rawReadLower G) σf σg)
    (hstart : E.initial=(sourceFrozenGeneralMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit).start ())
    (hΛ : 0<Λ) (hLaΛ : anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε)
    (hlip : ∀ x y,‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖≤Λ*‖x-y‖)
    (hlower : ∀ x,lower≤P.hyperobjective P.canonicalResponse x)
    (hgap : P.hyperobjective P.canonicalResponse x₀-lower≤Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖≤R₀) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ z,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse)
      (CachedOracleCode.selected Λ Δ ε x₀
        (z.1,HistoryProgram.stoppedOutput
          (sourceFrozenGeneralMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit).program
          (experimentPath E.state z.2)))‖)
      ∂(StochasticOuter.uniformLaw (outerCount Λ Δ ε)).prod E.law)≤ENNReal.ofReal ε ∧
    E.actualCost≤ENNReal.ofReal (CachedUpper.rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  exact source_frozen_general_upper P x₀ yinit lower E hstart hΛ hLaΛ hΔ hε hlip hlower hgap hinit

end GeneralSource
end Bilevel.PolishedHistory
