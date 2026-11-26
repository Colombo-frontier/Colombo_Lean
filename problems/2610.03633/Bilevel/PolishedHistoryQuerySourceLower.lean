import Bilevel.PolishedHistoryQuerySourceStationary
import Bilevel.PolishedHistoryMinimaxLower

/-! Actual query-adapted source lower transfer with arbitrary mean predicates.
Positive source dimensions and prescribed mean curvature are instantiated,
not represented by assumed complexity inequalities. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {μ L ρ Δ R₀ σf σg : ℝ}

theorem stationary_minimax_le_query_source
    (C : PrimitiveQuery.InstanceClass μ L ρ Δ R₀ σf σg) (D : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) (ε : ℝ)
    (hcons : ∀ G (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg),C G I → I.IsConservative)
    (hmean : ∀ G (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg),C G I → D G (stationarySourceMean I)) :
    PrimitiveQuery.Complexity C ε≤queryPostComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) D conservative ε := by
  unfold queryPostComplexity PrimitiveQuery.Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  let oldSolver : PrimitiveQuery.Solver := fun G => (A.val G 0 0).compile
  have hacc : PrimitiveQuery.Accurate C ε oldSolver := by
    intro G I hI
    have h := A.property (stationaryQueryPostChallenge I A.val) (hmean G I hI)
      (fun _ => stationaryQueryExecution_conservative I (A.val G 0 0).bodyAsAlgorithm (hcons G I hI))
    change (stationaryQueryExecution I (A.val G 0 0).bodyAsAlgorithm).postRisk≤ENNReal.ofReal ε at h
    rw [← query_post_compile_risk I (A.val G 0 0)] at h
    exact h
  refine (iInf_le _ ⟨oldSolver,hacc⟩).trans ?_
  apply iSup_le
  intro I
  change I.val.2.cost ((A.val I.val.1 0 0).compile)≤queryPostWorstCost D conservative A.val
  rw [query_post_compile_cost I.val.2 (A.val I.val.1 0 0)]
  exact le_iSup_of_le ⟨stationaryQueryPostChallenge I.val.2 A.val,⟨hmean I.val.1 I.val.2 I.property,
    fun _ => stationaryQueryExecution_conservative I.val.2 (A.val I.val.1 0 0).bodyAsAlgorithm
      (hcons I.val.1 I.val.2 I.property)⟩⟩ le_rfl

theorem stationary_conservative_le_positive_query_source (conservative : Bool) (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
      queryPostComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
        (positiveSourceClass (fun _ _ => True)) conservative ε := by
  apply (stationary_complexity_le_positive _ ε).trans
  apply stationary_minimax_le_query_source
    (PolishedPositiveDimension.positiveClass (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg))) _ conservative ε
  · exact fun _ _ h => h.1
  · exact fun _ _ h => ⟨True.intro,h.2⟩

theorem stationary_curvature_le_positive_query_source (Λ : ℝ) (conservative : Bool) (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε≤
      queryPostComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
        (positiveSourceClass (sourceCurvatureClass Λ)) conservative ε := by
  apply (stationary_complexity_le_positive _ ε).trans
  apply stationary_minimax_le_query_source
    (PolishedPositiveDimension.positiveClass (PrimitiveQuery.conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) Λ)) _ conservative ε
  · exact fun _ _ h => h.1.1
  · exact fun _ _ h => ⟨h.1.2,h.2⟩

/-- The original source-positive dimensions, both conservative and
unrestricted source classes, and one common universal lower-rate witness. -/
theorem uniform_positive_query_source_classes_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      ∀ conservative : Bool,
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        queryPostComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (fun _ _ => True)) conservative ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hl⟩ := ChiUniformLower.uniform_both_classes_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc conservative
  exact (hl L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc).1.trans
    (stationary_conservative_le_positive_query_source conservative ε)

end Bilevel.PolishedHistory
