import Bilevel.PolishedHistoryUpperSolver

/-! The independent public output index changes only the selected output;
the hidden terminal history and original-call counter remain joint. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry OracleCode Stateful CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {G : PrimitiveQuery.Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

theorem Instance.denote_selected_calls_integral (ε : ℝ) (h : I.History) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable
        (CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
          μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit)).law (j,h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε))=
    ∫⁻ y,(y.2.2:ℝ≥0∞) ∂(CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have he (j : Fin (outerCount Λ Δ ε)) :
      (∫⁻ y,(y.2.2:ℝ≥0∞)
        ∂(OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable
          (CachedOracleCode.selectedAlgorithm μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit)).law (j,h))=
      ∫⁻ y,(y.2.2:ℝ≥0∞) ∂(CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h) := by
    rw [I.denote_selectedAlgorithm_law ε j h]
    have hf : Measurable (fun y : Outcome G.X I.History => (y.2.2:ℝ≥0∞)) :=
      (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_snd.comp measurable_snd)
    have hm : Measurable (fun z : Outcome (CachedOuterProcedure.State G.X G.Y) I.History =>
        (CachedOracleCode.selected Λ Δ ε I.x₀ (j,z.1),z.2)) :=
      ((CachedOracleCode.selected_measurable Λ Δ ε I.x₀).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    rw [lintegral_map hf hm]
  calc
    _ = ∫⁻ _j : Fin (outerCount Λ Δ ε),
        (∫⁻ y,(y.2.2:ℝ≥0∞) ∂(CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h))
        ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε) := lintegral_congr he
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem Instance.denote_selected_loss_integral (ε : ℝ) (h : I.History) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ j,∫⁻ y,ENNReal.ofReal (I.loss y.1)
      ∂(OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable
        (CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
          μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit)).law (j,h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε))=
    ∫⁻ z,ENNReal.ofReal (I.loss (CachedUpper.output Λ Δ ε I.x₀ z))
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε)
        ((CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h)) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have he (j : Fin (outerCount Λ Δ ε)) :
      (∫⁻ y,ENNReal.ofReal (I.loss y.1)
        ∂(OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable
          (CachedOracleCode.selectedAlgorithm μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit)).law (j,h))=
      ∫⁻ y,ENNReal.ofReal (I.loss (CachedOracleCode.selected Λ Δ ε I.x₀ (j,y.1)))
        ∂(CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h) := by
    rw [I.denote_selectedAlgorithm_law ε j h]
    have hf : Measurable (fun y : Outcome G.X I.History => ENNReal.ofReal (I.loss y.1)) :=
      (I.loss_measurable.comp measurable_fst).ennreal_ofReal
    have hm : Measurable (fun z : Outcome (CachedOuterProcedure.State G.X G.Y) I.History =>
        (CachedOracleCode.selected Λ Δ ε I.x₀ (j,z.1),z.2)) :=
      ((CachedOracleCode.selected_measurable Λ Δ ε I.x₀).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    rw [lintegral_map hf hm]
  have hm : Measurable (fun z : Fin (outerCount Λ Δ ε)×Outcome (CachedOuterProcedure.State G.X G.Y) I.History =>
      ENNReal.ofReal (I.loss (CachedOracleCode.selected Λ Δ ε I.x₀ (z.1,z.2.1)))) :=
    (I.loss_measurable.ennreal_ofReal).comp
      ((CachedOracleCode.selected_measurable Λ Δ ε I.x₀).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  calc
    _ = ∫⁻ j,∫⁻ y,ENNReal.ofReal (I.loss (CachedOracleCode.selected Λ Δ ε I.x₀ (j,y.1)))
      ∂(CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε) := lintegral_congr he
    _ = _ := (lintegral_prod _ hm.aemeasurable).symm

end Bilevel.PolishedHistory
