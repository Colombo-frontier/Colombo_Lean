import SampleReuse.SourceMainUpper
import SampleReuse.SourceBudgetRates
import SampleReuse.SourceLowerRates
import SampleReuse.SourceWorstCaseBudget

/-! Matching total complexity is expressed through actual operational
guarantees, rather than an unspecified minimax object. The upper algorithm
uses the proved measurable Rayleigh-witness selector; it does not claim
literal identity with a minimum-eigenvector implementation. The lower
quantifier order is the intended minimax order: every solver has a hard
instance, with independent gradient and curvature tolerances. -/

open SecondOrder MeasureTheory
open scoped ENNReal

namespace SampleReuse
noncomputable section

/-- A uniform cap on genuine pre-stop evaluations transfers the actual
expected-cost lower bound to worst-case deterministic query complexity. -/
theorem SourceUniformSolverLower.worst_case {M : Parameters} {d : ℕ} {ε γ rate : ℝ}
    (h : SourceUniformSolverLower M d ε γ rate)
    {H S Ξ : Type} [MeasurableSpace S] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (hmeas : MeasurableStoppingFamily P) (hop : SeparateOperationallyMeasurable P)
    (hsolve : SolvesSeparateFiniteInstances (M := M) μ P ε γ) (N : ℕ)
    (hcap : ∀ (I : FiniteScalarInstance M d) ξ tape,
      (P ξ).extendedCost (separateSampleReply I.sample) tape ≤ (N : ℝ≥0∞)) : rate≤(N:ℝ) := by
  obtain ⟨I,hI⟩ := h H S Ξ μ P hmeas hop hsolve
  exact separate_expected_lower_implies_worst_case μ P I N hI (hcap I)

/-- The actual upper program and actual uniform-solver lower bound, with
explicit logarithmic factors and the separate achievable derivative caps.
This does not assert a characterization of the two-resource Pareto frontier. -/
structure SourceMatchingAt (M : Parameters) (d : ℕ) (ε γ c : ℝ) : Prop where
  upper : SourceUpperGuarantee M d ε γ
  gradient_cap : (sourceGradientQueryCap M d ε γ:ℝ) ≤
    sourceGradientRateConstant M*(sourceRateLog M d ε γ)^4*(1/ε^3+1/(ε^2*γ))
  hessian_cap : (sourceHessianQueryCap M d ε γ:ℝ) ≤
    sourceHessianRateConstant M*(sourceRateLog M d ε γ)^4*(1/ε^2+1/(ε*γ^2)+1/γ^3)
  total_cap : ((sourceGradientQueryCap M d ε γ+sourceHessianQueryCap M d ε γ:ℕ):ℝ) ≤
    sourceTotalRateConstant M*(sourceRateLog M d ε γ)^4*(1/ε^3+1/γ^3)
  lower : SourceUniformSolverLower M d ε γ (c*(1/ε^3+1/γ^3)/(1+Real.log (1/ε)))

/-- The manuscript's matching-total-complexity corollary. For fixed positive
parameters, the upper constants and small-tolerance thresholds do not depend
on either tolerance or dimension. The tolerances are chosen independently.
The upper program succeeds on every admissible model and obeys deterministic
separate caps; the lower bound applies to actual expected stopping cost. -/
theorem source_matching_total_complexity (M : Parameters) :
    ∃ c Cd ε₀ γ₀ : ℝ, 0<c ∧ 0<Cd ∧ 0<ε₀ ∧ 0<γ₀ ∧ ε₀≤1 ∧ γ₀≤1 ∧
      ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ<γ₀ →
      ∃ dstar : ℕ,
        (dstar:ℝ) ≤ Cd*(1+M.gap*(slowBlockSize M ε:ℝ)^(3/4:ℝ)/ε+
          Real.log (2/γ)/γ^4+1/γ^3) ∧
      ∀ d : ℕ, dstar≤d → SourceMatchingAt M d ε γ c := by
  obtain ⟨c,Cd,ε₀,γ₀,hc,hCd,hε₀,hγ₀,he₀,hg₀,hmain⟩ := source_lower_logarithmic M
  refine ⟨c,Cd,ε₀,γ₀,hc,hCd,hε₀,hγ₀,he₀,hg₀,?_⟩
  intro ε γ hε he hγ hg
  obtain ⟨dstar,hdstar,hmain⟩ := hmain ε γ hε he hγ hg
  refine ⟨dstar,hdstar,?_⟩
  intro d hd
  refine ⟨source_upper_guarantee M d hε hγ,?_,?_,?_,hmain d hd⟩
  · exact source_gradient_cap_rate M d hε (he.trans he₀) hγ
  · exact source_hessian_cap_rate M d hε (he.trans he₀) hγ (hg.le.trans hg₀)
  · simpa only [Nat.cast_add,sourceGradientQueryCap,sourceHessianQueryCap] using
      source_total_cap_rate M d hε (he.trans he₀) hγ (hg.le.trans hg₀)

/-- The rates are bounds on the actual evaluated prefix, ending at the first
finished state of the program, for every tape and private-sign realization. -/
theorem SourceMatchingAt.actual_counts {M : Parameters} {d : ℕ} {ε γ c : ℝ}
    (h : SourceMatchingAt M d ε γ c) {Ω : Type} (x₀ : Point d) (F : Ω→Point d→ℝ)
    (tape : SampleTape (sourceHandleCount M d ε γ) Ω)
    (bits : Fin (sourceIterationCap M ε γ)→Bool) :
    ((sourceUpperQueryCounts M d ε γ x₀ F tape bits).1:ℝ) ≤
      sourceGradientRateConstant M*(sourceRateLog M d ε γ)^4*(1/ε^3+1/(ε^2*γ)) ∧
    ((sourceUpperQueryCounts M d ε γ x₀ F tape bits).2:ℝ) ≤
      sourceHessianRateConstant M*(sourceRateLog M d ε γ)^4*(1/ε^2+1/(ε*γ^2)+1/γ^3) := by
  have hc := h.upper.counts x₀ F tape bits
  exact ⟨(Nat.cast_le.mpr hc.1).trans h.gradient_cap,(Nat.cast_le.mpr hc.2).trans h.hessian_cap⟩

theorem SourceMatchingAt.actual_total {M : Parameters} {d : ℕ} {ε γ c : ℝ}
    (h : SourceMatchingAt M d ε γ c) {Ω : Type} (x₀ : Point d) (F : Ω→Point d→ℝ)
    (tape : SampleTape (sourceHandleCount M d ε γ) Ω)
    (bits : Fin (sourceIterationCap M ε γ)→Bool) :
    (sourceUpperStop M d ε γ x₀ F tape bits:ℝ) ≤
      sourceTotalRateConstant M*(sourceRateLog M d ε γ)^4*(1/ε^3+1/γ^3) :=
  (Nat.cast_le.mpr (h.upper.stops x₀ F tape bits)).trans h.total_cap

end
end SampleReuse
