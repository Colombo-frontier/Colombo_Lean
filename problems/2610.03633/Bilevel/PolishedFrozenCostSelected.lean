import Bilevel.PolishedFrozenCost
import Bilevel.PolishedCompiledHistoryLaw

/-! Exact arbitrary-history denotation of the independent uniform terminal
index for the literal frozen code, retaining terminal history and calls. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedFrozenProcedure
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedBudgetCalibration
variable {X Y History : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query:=X×Y) (History:=History) (X:=X) (Y:=Y) σf σg)

def rawOracle : HistoryProgram.Oracle (X×Y) (FullResponse X Y) History where
  law := O.law
  markov := inferInstance
  update := O.update
  update_measurable := O.update_measurable

theorem denote_selected_law (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y)
    (j : Fin (outerCount Λ Δ ε)) (h : History) :
    (OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
      (PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h)=
    ((algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)).map
      (fun z => (CachedOracleCode.selected Λ Δ ε x₀ (j,z.1),z.2)) := by
  rw [PolishedFrozenCode.selectedAlgorithm,OracleCode.History.denote_map,Procedure.map_law]
  change ((OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
    (PolishedFrozenCode.algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law ((),h)).map _=_
  rw [PolishedFrozenCode.History.denote_algorithm (H:=of History) O]

theorem selected_calls_integral (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) (h : History) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
        (PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε))=
    ∫⁻ y,(y.2.2:ℝ≥0∞) ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h) := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have he (j : Fin (outerCount Λ Δ ε)) :
      (∫⁻ y,(y.2.2:ℝ≥0∞)
        ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
          (PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h))=
      ∫⁻ y,(y.2.2:ℝ≥0∞) ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h) := by
    rw [denote_selected_law O]
    have hf : Measurable (fun y : Outcome X History => (y.2.2:ℝ≥0∞)) :=
      (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_snd.comp measurable_snd)
    have hm : Measurable (fun z : Outcome (State X Y) History =>
        (CachedOracleCode.selected Λ Δ ε x₀ (j,z.1),z.2)) :=
      ((CachedOracleCode.selected_measurable Λ Δ ε x₀).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    rw [lintegral_map hf hm]
  calc
    _ = ∫⁻ _j : Fin (outerCount Λ Δ ε),
        (∫⁻ y,(y.2.2:ℝ≥0∞) ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h))
        ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε) := lintegral_congr he
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem selected_loss_integral (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) (h : History)
    (loss : X → ℝ) (hloss : Measurable loss) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ j,∫⁻ y,ENNReal.ofReal (loss y.1)
      ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
        (PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε))=
    ∫⁻ z,ENNReal.ofReal (loss (CachedUpper.output Λ Δ ε x₀ z))
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε)
        ((algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)) := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have he (j : Fin (outerCount Λ Δ ε)) :
      (∫⁻ y,ENNReal.ofReal (loss y.1)
        ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
          (PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h))=
      ∫⁻ y,ENNReal.ofReal (loss (CachedOracleCode.selected Λ Δ ε x₀ (j,y.1)))
        ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h) := by
    rw [denote_selected_law O]
    have hf : Measurable (fun y : Outcome X History => ENNReal.ofReal (loss y.1)) :=
      (hloss.comp measurable_fst).ennreal_ofReal
    have hm : Measurable (fun z : Outcome (State X Y) History =>
        (CachedOracleCode.selected Λ Δ ε x₀ (j,z.1),z.2)) :=
      ((CachedOracleCode.selected_measurable Λ Δ ε x₀).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    rw [lintegral_map hf hm]
  have hm : Measurable (fun z : Fin (outerCount Λ Δ ε)×Outcome (State X Y) History =>
      ENNReal.ofReal (loss (CachedOracleCode.selected Λ Δ ε x₀ (z.1,z.2.1)))) :=
    (hloss.ennreal_ofReal).comp ((CachedOracleCode.selected_measurable Λ Δ ε x₀).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  calc
    _ = ∫⁻ j,∫⁻ y,ENNReal.ofReal (loss (CachedOracleCode.selected Λ Δ ε x₀ (j,y.1)))
      ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε) := lintegral_congr he
    _ = _ := (lintegral_prod _ hm.aemeasurable).symm

end Bilevel.PolishedFrozenProcedure
