import Bilevel.CachedOracleCodeAlgorithm
import Bilevel.CachedOracleHistoryOuter

/-! The calibrated cached algorithm as public causal code. The only private
input is its independent uniform output index; every stochastic operation
in the body is one of the actual original full-oracle calls. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode.History
open Stateful PrimitiveGeometry OracleCode CachedBudgetCalibration CachedParameterChoice
variable {X Y : Type} {H : OracleCode.Space}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

theorem denote_algorithm (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)=
      CachedUpper.algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit := by
  unfold algorithm CachedUpper.algorithm CachedOuterProcedure.publicRun
  simpa using (denote_run O
    (μ:=μ) (Lg:=Lg) (Cf:=Cf)
    (t:=tilt (CachedUpper.bias μ Lg Cf ρ) ε)
    (D:=CachedUpper.initialRadius μ Lg Cf (tilt (CachedUpper.bias μ Lg Cf ρ) ε) Λ Δ ε R₀)
    (r:=lowerRadius Lg (CachedUpper.bias μ Lg Cf ρ) ε)
    (rA:=anchorRadius Lf Lg (Lg/μ) (CachedUpper.bias μ Lg Cf ρ) ε)
    (δ:=gradientRadius (CachedUpper.bias μ Lg Cf ρ) ε)
    (η:=upperRadius (Lg/μ) ε) (Λ:=Λ) (cap:=energyCap Λ Δ ε)
    (radius:=refreshRadius Λ (anchorSmoothness Lf (Lg/μ)) Δ ε)
    (q:=CachedUpper.repetitions Λ Δ ε)
    (x₀:=x₀) (yinit:=yinit) (n:=outerCount Λ Δ ε))

end Bilevel.CachedOracleCode.History
