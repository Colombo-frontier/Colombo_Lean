import Bilevel.PolishedHistorySourcePostRun
import Bilevel.PolishedHistorySourcePostOrdinary

/-! Source-wide lower bounds for arbitrary randomized bodies and arbitrary
independent terminal selections. The hard challenges are actual conditional
probability-space experiments, not an assumed execution embedding. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {μ L ρ Δ R₀ σf σg : ℝ}

variable {G : Geometry} (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)

def stationaryPostSourceChallenge (A : PostSolverAt) : PostSourceChallenge A μ L ρ Δ R₀ σf σg where
  geometry:=G
  mean:=stationarySourceMean I
  execution:=stationarySourceExecution I (A G 0 0).bodyAsAlgorithm

/-- All source algorithms are covered: their arbitrary independent
terminal selection is compiled into an ordinary algorithm only on the
fresh hard subclass, with exact stopped cost and risk. -/
theorem stationary_minimax_le_post_source (conservative : Bool) (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
      postSourceComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε := by
  unfold postSourceComplexity PrimitiveQuery.Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  let oldSolver : PrimitiveQuery.Solver := fun G => (A.val G 0 0).compile
  have hacc : PrimitiveQuery.Accurate (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε oldSolver := by
    intro G I hI
    have h := A.property (stationaryPostSourceChallenge I A.val)
      (fun _ => stationarySourceExecution_conservative I (A.val G 0 0).bodyAsAlgorithm hI)
    change (stationarySourceExecution I (A.val G 0 0).bodyAsAlgorithm).postRisk≤ENNReal.ofReal ε at h
    rw [← post_compile_risk I (A.val G 0 0)] at h
    exact h
  refine (iInf_le _ ⟨oldSolver,hacc⟩).trans ?_
  apply iSup_le
  intro I
  change I.val.2.cost ((A.val I.val.1 0 0).compile)≤postSourceWorstCost conservative A.val
  rw [post_compile_cost I.val.2 (A.val I.val.1 0 0)]
  exact le_iSup_of_le ⟨stationaryPostSourceChallenge I.val.2 A.val,
    fun _ => stationarySourceExecution_conservative I.val.2 (A.val I.val.1 0 0).bodyAsAlgorithm I.property⟩ le_rfl

/-- The actual full source conditional classes, with one common set of
universal constants for conservative and unrestricted responses. No
FreshSourceEmbedding, locality, or final-rate premise occurs. -/
theorem uniform_post_source_classes_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      ∀ conservative : Bool,
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        postSourceComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hl⟩ := ChiUniformLower.uniform_both_classes_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc conservative
  exact (hl L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc).1.trans
    (stationary_minimax_le_post_source conservative ε)

end Bilevel.PolishedHistory
