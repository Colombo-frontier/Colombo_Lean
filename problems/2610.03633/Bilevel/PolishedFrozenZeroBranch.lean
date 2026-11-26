import Bilevel.PolishedFrozenProcedure
import Bilevel.PolishedFrozenCalls
import Bilevel.CachedUpperTheorem

/-! The literal algorithm's public zero-call branch. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenCode
open Stateful PrimitiveGeometry OracleCode CachedBudgetCalibration CachedOracleCode
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

open Classical in
def sourceSelectedAlgorithm (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    Flow (X:=X) (Y:=Y) (Fin (outerCount Λ Δ ε)) X :=
  .choose (fun i => if i=0 then .pure (fun _ => x₀) measurable_const else
    selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)
    (fun _ => if 2*Λ*Δ≤ε^2 then 0 else 1) measurable_const

omit [CompleteSpace X] [CompleteSpace Y] in
theorem sourceSelectedAlgorithm_large {Seed : Type*}
    (response : (X × Y) → Seed → FullResponse X Y)
    (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y)
    (hl : 2*Λ*Δ≤ε^2) (z : Fin (outerCount Λ Δ ε) × IndependentStream.Stream Seed) :
    eval response (sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) z=
      ((x₀,(),0),z.2) := by
  simp only [sourceSelectedAlgorithm,eval,if_pos hl,ite_true]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem sourceSelectedAlgorithm_small {Seed : Type*}
    (response : (X × Y) → Seed → FullResponse X Y)
    (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y)
    (hl : ¬2*Λ*Δ≤ε^2) (z : Fin (outerCount Λ Δ ε) × IndependentStream.Stream Seed) :
    eval response (sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) z=
      eval response (selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) z := by
  simp only [sourceSelectedAlgorithm,eval,if_neg hl,Nat.one_ne_zero,ite_false]

namespace History
variable {H : Space} {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

private theorem procedure_law_injective {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    Function.Injective (fun p : Procedure A B C => p.law) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

theorem denote_sourceSelectedAlgorithm (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)=
    if 2*Λ*Δ≤ε^2 then Procedure.pure (fun _ => x₀) measurable_const else
      OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
        (selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) := by
  classical
  apply procedure_law_injective
  by_cases hl : 2*Λ*Δ≤ε^2
  · ext z s
    rcases z with ⟨p,h⟩
    simp only [sourceSelectedAlgorithm,OracleCode.History.denote,if_pos hl,ite_true,Procedure.choose_law]
  · ext z s
    rcases z with ⟨p,h⟩
    simp only [sourceSelectedAlgorithm,OracleCode.History.denote,if_neg hl,Nat.one_ne_zero,ite_false,Procedure.choose_law]

end History
end Bilevel.PolishedFrozenCode
