import Bilevel.PolishedFrozenCostSelected
import Bilevel.PolishedFrozenUpperAccuracy

/-! Actual stopped execution certificates for the literal frozen code under
arbitrary conditional history kernels. Zero-query top-level dispatch can be
added by the source wrapper without changing these positive-run results. -/
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

theorem compiled_calls_le (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (h : History)
    (q₀ : X×Y) (o₀ : FullResponse X Y) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let c := PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    (∫⁻ w,HistoryProgram.totalCalls m.program w
      ∂HistoryProgram.trajectoryLaw m.program (rawOracle O)
        (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) m.start h)≤
      ENNReal.ofReal (CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let c := PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
  have hb := PolishedCompiledHistory.compiled_stopped_calls_le
    (Q:=of (X×Y)) (O:=of (FullResponse X Y)) (A:=of (Fin (outerCount Λ Δ ε))) (B:=of X) (H:=of History)
    (rawOracle O) q₀ o₀ c (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) h
  exact hb.trans ((selected_calls_integral O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit h).le.trans
    (algorithm_cost_lintegral O μ Lf Lg Cf ρ Λ Δ ε R₀ hLf hΛ hLaΛ hΔ hε x₀ yinit h))

theorem compiled_risk_le_denote (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (h : History)
    (q₀ : X×Y) (o₀ : FullResponse X Y) (loss : X → ℝ) (hloss : Measurable loss) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let c := PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput m.program w))
      ∂HistoryProgram.trajectoryLaw m.program (rawOracle O)
        (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) m.start h)≤
    ∫⁻ z,ENNReal.ofReal (loss (CachedUpper.output Λ Δ ε x₀ z))
      ∂StochasticOuter.outputLaw (outerCount Λ Δ ε)
        ((algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h)) := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let c := PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
  have hb := algorithm_cost_lintegral O μ Lf Lg Cf ρ Λ Δ ε R₀ hLf hΛ hLaΛ hΔ hε x₀ yinit h
  have hc : (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable c).law (j,h)
        ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε))≠⊤ := by
    rw [selected_calls_integral O]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hr := PolishedCompiledHistory.compiled_stopped_loss_le
    (Q:=of (X×Y)) (O:=of (FullResponse X Y)) (A:=of (Fin (outerCount Λ Δ ε))) (B:=of X) (H:=of History)
    (rawOracle O) q₀ o₀ c (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) h hc loss hloss
  exact hr.trans_eq (selected_loss_integral O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit h loss hloss)

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ) [FiniteDimensional ℝ Y] [Nontrivial Y]

/-- Actual first-halt risk and original calls of the executed frozen-anchor
algorithm. The reuse estimator, five-group refresh, all-history cost, and
conditional-kernel compiler semantics are all instantiated. -/
theorem compiled_accuracy_and_cost
    (hfx : ∀ x y,O.upper.truth_x (x,y)=P.fx x y)
    (hfy : ∀ x y,O.upper.truth_y (x,y)=P.fy x y)
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    {Λ Δ ε R₀ lower : ℝ} (hΛ : 0<Λ) (hΔ : 0≤Δ) (hε : 0<ε)
    (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hlip : ∀ x y,‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖≤Λ*‖x-y‖)
    (hlower : ∀ x,lower≤P.hyperobjective P.canonicalResponse x)
    (x₀ : X) (yinit : Y) (hgap : P.hyperobjective P.canonicalResponse x₀-lower≤Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖≤R₀) (h : History)
    (q₀ : X×Y) (o₀ : FullResponse X Y) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let c := PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    let ν := HistoryProgram.trajectoryLaw m.program (rawOracle O)
      (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) m.start h
    (∫⁻ w,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse)
      (HistoryProgram.stoppedOutput m.program w)‖) ∂ν)≤ENNReal.ofReal ε ∧
    (∫⁻ w,HistoryProgram.totalCalls m.program w ∂ν)≤
      ENNReal.ofReal (CachedUpper.rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  have ha := PolishedFrozenUpper.accuracy O P hfx hfy hgy hgx hΛ hΔ hε hlip hlower x₀ yinit hgap hinit h
  have hm : Measurable (fun x => ‖gradient (P.hyperobjective P.canonicalResponse) x‖) :=
    (P.gradient_hyperobjective_lipschitz P.canonicalResponse).continuous.measurable.norm
  constructor
  · refine (compiled_risk_le_denote O μ Lf Lg Cf ρ Λ Δ ε R₀ P.Lf_nonneg hΛ hLaΛ hΔ hε
      x₀ yinit h q₀ o₀ _ hm).trans ?_
    rw [←ofReal_integral_eq_lintegral_ofReal ha.1 (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal ha.2
  · exact (compiled_calls_le O μ Lf Lg Cf ρ Λ Δ ε R₀ P.Lf_nonneg hΛ hLaΛ hΔ hε x₀ yinit h q₀ o₀).trans
      (ENNReal.ofReal_le_ofReal (CachedUpper.cost_le_rateBound P.μ_pos P.strong_convexity_le_smoothness
        P.Lf_nonneg P.ρ_nonneg hΛ hLaΛ hΔ hε))

end Bilevel.PolishedFrozenProcedure
