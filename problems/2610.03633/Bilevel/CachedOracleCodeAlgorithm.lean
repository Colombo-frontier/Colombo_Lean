import Bilevel.CachedOracleCodeOuter

/-! The calibrated cached algorithm as public causal code. The only private
input is its independent uniform output index; every stochastic operation
in the body is one of the actual original full-oracle calls. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode
open Stateful PrimitiveGeometry OracleCode CachedBudgetCalibration CachedParameterChoice
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def algorithm (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    Flow (X:=X) (Y:=Y) Unit (CachedOuterProcedure.State X Y) :=
  let k := Lg/μ
  let E := CachedUpper.bias μ Lg Cf ρ
  let t := tilt E ε
  run μ Lg Cf σf σg t (CachedUpper.initialRadius μ Lg Cf t Λ Δ ε R₀)
    (lowerRadius Lg E ε) (anchorRadius Lf Lg k E ε) (gradientRadius E ε) (upperRadius k ε)
    Λ (energyCap Λ Δ ε) (refreshRadius Λ (anchorSmoothness Lf k) Δ ε)
    (CachedUpper.repetitions Λ Δ ε) x₀ yinit (outerCount Λ Δ ε)

def selected (Λ Δ ε : ℝ) (x₀ : X)
    (z : Fin (outerCount Λ Δ ε) × CachedOuterProcedure.State X Y) : X :=
  CappedExecution.output Λ (energyCap Λ Δ ε) x₀ z.2.1 (outerCount Λ Δ ε) z.1

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem selected_measurable (Λ Δ ε : ℝ) (x₀ : X) :
    Measurable (selected (Y:=Y) Λ Δ ε x₀) := by
  have hm : Measurable (fun z : CachedOuterProcedure.State X Y × Fin (outerCount Λ Δ ε) =>
      CappedExecution.output Λ (energyCap Λ Δ ε) x₀ z.1.1 (outerCount Λ Δ ε) z.2) :=
    measurable_from_prod_countable (fun i =>
      CappedExecution.output_measurable Λ (energyCap Λ Δ ε) x₀
        (fun j (s : CachedOuterProcedure.State X Y) => s.1 j)
        (fun j => (measurable_pi_apply j).comp measurable_fst)
        (outerCount Λ Δ ε) i)
  exact hm.comp measurable_swap

def selectedAlgorithm (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    Flow (X:=X) (Y:=Y) (Fin (outerCount Λ Δ ε)) X :=
  OracleCode.map (.reparam (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)
    (fun _ => ()) measurable_const) (selected Λ Δ ε x₀) (selected_measurable Λ Δ ε x₀)

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=Unit) (X:=X) (Y:=Y) σf σg)
  (K : Kernel (X × Y) (FullResponse X Y)) [IsMarkovKernel K]
  (hK : ∀ q,O.law (q,())=K q)

include hK in
theorem denote_algorithm (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    denote K (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)=
      CachedUpper.algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit := by
  unfold algorithm CachedUpper.algorithm CachedOuterProcedure.publicRun
  simpa using (denote_run O K hK
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

end Bilevel.CachedOracleCode
