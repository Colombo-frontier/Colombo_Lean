import Smoothness2601.HardQualitative
import Smoothness2601.CoordinateMinimax

/-! The actual minimax classes with joint C-infinity regularity, optionally
also lower-variable real analyticity, and no common higher-derivative budgets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
open scoped ContDiff ENNReal
namespace Smoothness2601

def QualitativeBudgetWorks (b : Budgets) (analytic : Bool) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ dx dy : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) (Euclidean dy),
    ∀ P : Population (X := Euclidean dx) (Y := Euclidean dy) b,
    P.JointlySmooth → (analytic = true → P.LowerAnalytic) →
    ∀ x₀ y₀, P.Initialized x₀ y₀ →
    ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
      ∀ (O : Adaptive.Oracle P H) (h : H), Adaptive.Succeeds A O N ε h x₀ y₀

def qualitativeMinimaxComplexity (b : Budgets) (analytic : Bool) (ε : ℝ) : ℝ≥0∞ :=
  sInf {n | ∃ N : ℕ, n = (N : ℝ≥0∞) ∧ QualitativeBudgetWorks b analytic ε N}

theorem baseline_budget_qualitative {b : Budgets} {L : ℕ → ℝ} {ε : ℝ} {N : ℕ}
    (hN : BudgetWorks b 1 L ε N) (analytic : Bool) : QualitativeBudgetWorks b analytic ε N := by
  intro dx dy
  obtain ⟨A,hA⟩ := hN dx dy
  refine ⟨A,?_⟩
  intro P _ _
  apply hA P
  intro q hq hp
  have hh : q+1 ≤ 1 := by exact_mod_cast hp
  omega

theorem qualitative_minimax_le_baseline (b : Budgets) (L : ℕ → ℝ) (analytic : Bool) (ε : ℝ) :
    qualitativeMinimaxComplexity b analytic ε ≤ minimaxComplexity b 1 L ε := by
  apply sInf_le_sInf
  rintro n ⟨N,rfl,hN⟩
  exact ⟨N,rfl,baseline_budget_qualitative hN analytic⟩

section Transport
variable {X Y Z : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  {b : Budgets} (P : Population (X := X) (Y := Y) b) (e : Z ≃ₗᵢ[ℝ] Y)

theorem qualitative_transport_smooth (hP : P.JointlySmooth) :
    (CoordinatePopulation.transport P e).JointlySmooth :=
  ⟨hP.1.comp (CoordinateGeometry.joint (X := X) e).toContinuousLinearEquiv.contDiff,
    hP.2.comp (CoordinateGeometry.joint (X := X) e).toContinuousLinearEquiv.contDiff⟩

theorem qualitative_transport_analytic (hP : P.LowerAnalytic) :
    (CoordinatePopulation.transport P e).LowerAnalytic := by
  intro x z
  have he := e.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt z
  exact ⟨(hP x (e z)).1.comp he,(hP x (e z)).2.comp he⟩

end Transport

theorem qualitative_budgetWorks_scalar {b : Budgets} {analytic : Bool} {ε : ℝ} {N : ℕ}
    (hN : QualitativeBudgetWorks b analytic ε N) :
    ∀ dx : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) ℝ,
      ∀ P : Population (X := Euclidean dx) (Y := ℝ) b,
      P.JointlySmooth → (analytic = true → P.LowerAnalytic) →
      ∀ x₀ y₀, P.Initialized x₀ y₀ →
      ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
        ∀ (O : Adaptive.Oracle P H) (h : H), Adaptive.Succeeds A O N ε h x₀ y₀ := by
  intro dx
  obtain ⟨A,hA⟩ := hN dx 1
  let e := CoordinateMinimax.scalarEquiv
  refine ⟨CoordinateAlgorithm.pull A e,?_⟩
  intro P hs ha x₀ y₀ hi H inst O h
  apply CoordinateAlgorithm.succeeds A e P O N ε h x₀ y₀
  exact hA (CoordinatePopulation.transport P e) (qualitative_transport_smooth P e hs)
    (fun htrue => qualitative_transport_analytic P e (ha htrue))
    x₀ (e.symm y₀) (CoordinatePopulation.initialized P e hi)
    H inst (CoordinateOracle.transport P e O) h

theorem qualitative_lower_of_obstruction {b : Budgets} {analytic : Bool} {ε threshold : ℝ}
    (h : ∀ N : ℕ, (N:ℝ) < threshold → ¬QualitativeBudgetWorks b analytic ε N) :
    ENNReal.ofReal threshold ≤ qualitativeMinimaxComplexity b analytic ε := by
  apply le_sInf
  rintro n ⟨N,rfl,hN⟩
  have hh : threshold ≤ (N:ℝ) := le_of_not_gt (fun hn => h N hn hN)
  exact_mod_cast ENNReal.ofReal_le_ofReal hh

end Smoothness2601
