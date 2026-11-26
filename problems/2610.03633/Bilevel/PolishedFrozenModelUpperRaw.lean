import Bilevel.PolishedFrozenCostCompiled
import Bilevel.PolishedFrozenZeroBranch

/-! The full literal algorithm, including its public zero-query branch,
under the actual arbitrary-history compiled stopping semantics. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedFrozenProcedure
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedBudgetCalibration
set_option maxHeartbeats 1400000
variable {X Y History : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query:=X×Y) (History:=History) (X:=X) (Y:=Y) σf σg)

theorem source_selected_lintegral (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) (h : History)
    (g : Outcome X History → ℝ≥0∞) (hg : Measurable g) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ j,∫⁻ y,g y
      ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
        (PolishedFrozenCode.sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h)
      ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε))=
    if 2*Λ*Δ≤ε^2 then g (x₀,h,0) else
      ∫⁻ j,∫⁻ y,g y
        ∂(OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable
          (PolishedFrozenCode.selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)).law (j,h)
        ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε) := by
  classical
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  rw [PolishedFrozenCode.History.denote_sourceSelectedAlgorithm (H:=of History) O]
  by_cases hl : 2*Λ*Δ≤ε^2
  · rw [if_pos hl,if_pos hl]
    have he (j : Fin (outerCount Λ Δ ε)) :
        (∫⁻ y,g y ∂(Procedure.pure (fun _ : Fin (outerCount Λ Δ ε) => x₀) measurable_const).law (j,h))=g (x₀,h,0) := by
      rw [Procedure.pure_law,lintegral_dirac' _ hg]
    calc
      _ = ∫⁻ _j : Fin (outerCount Λ Δ ε),g (x₀,h,0) ∂StochasticOuter.uniformLaw (outerCount Λ Δ ε) := lintegral_congr he
      _ = _ := by rw [lintegral_const,measure_univ,mul_one]
  · rw [if_neg hl,if_neg hl]

/-- The public large-accuracy branch has exactly zero actual stopping cost,
for every history kernel and without any stochastic moment hypothesis. -/
theorem source_compiled_zero_calls (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) (h : History)
    (hlarge : 2*Λ*Δ≤ε^2) (q₀ : X×Y) (o₀ : FullResponse X Y) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    let c := PolishedFrozenCode.sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    (∫⁻ w,HistoryProgram.totalCalls m.program w ∂HistoryProgram.trajectoryLaw m.program (rawOracle O)
      (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) m.start h)=0 := by
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let c := PolishedFrozenCode.sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
  have hn : Measurable (fun y : Outcome X History => (y.2.2:ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_snd.comp measurable_snd)
  have he := source_selected_lintegral O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit h _ hn
  rw [if_pos hlarge] at he
  simp only [Prod.snd,Nat.cast_zero] at he
  have hb := PolishedCompiledHistory.compiled_stopped_calls_le
    (Q:=of (X×Y)) (O:=of (FullResponse X Y)) (A:=of (Fin (outerCount Λ Δ ε))) (B:=of X) (H:=of History)
    (rawOracle O) q₀ o₀ c (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) h
  exact le_antisymm (hb.trans he.le) (zero_le _)

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ) [FiniteDimensional ℝ Y] [Nontrivial Y]

/-- The named frozen algorithm, on all accuracy ranges, is executed by one
public causal program. Both zero-query and capped reused-anchor branches
satisfy the actual first-halt accuracy and original-call budget. -/
theorem source_compiled_accuracy_and_cost
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
    let c := PolishedFrozenCode.sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    let ν := HistoryProgram.trajectoryLaw m.program (rawOracle O)
      (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) m.start h
    (∫⁻ w,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse)
      (HistoryProgram.stoppedOutput m.program w)‖) ∂ν)≤ENNReal.ofReal ε ∧
    (∫⁻ w,HistoryProgram.totalCalls m.program w ∂ν)≤
      ENNReal.ofReal (CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  classical
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let c := PolishedFrozenCode.sourceSelectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
  let ξ := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
  let D := OracleCode.History.denote (H:=of History) O.law O.update O.update_measurable c
  have hn : Measurable (fun y : Outcome X History => (y.2.2:ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_snd.comp measurable_snd)
  have hcost : (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞) ∂D.law (j,h) ∂ξ)≤
      ENNReal.ofReal (CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
    have he := source_selected_lintegral O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit h _ hn
    change (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞) ∂D.law (j,h) ∂ξ)=_ at he
    rw [he]
    split_ifs with hl
    · simp only [Prod.snd,Nat.cast_zero]
      exact zero_le _
    · rw [selected_calls_integral O]
      exact algorithm_cost_lintegral O μ Lf Lg Cf ρ Λ Δ ε R₀ P.Lf_nonneg hΛ hLaΛ hΔ hε x₀ yinit h
  have hfinite : (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞) ∂D.law (j,h) ∂ξ)≠⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcost
  have hloss : Measurable (fun x => ‖gradient (P.hyperobjective P.canonicalResponse) x‖) :=
    (P.gradient_hyperobjective_lipschitz P.canonicalResponse).continuous.measurable.norm
  have hrisk : (∫⁻ j,∫⁻ y,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse) y.1‖)
      ∂D.law (j,h) ∂ξ)≤ENNReal.ofReal ε := by
    have he := source_selected_lintegral O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit h
      (fun y => ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse) y.1‖))
      (hloss.comp measurable_fst).ennreal_ofReal
    change (∫⁻ j,∫⁻ y,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse) y.1‖) ∂D.law (j,h) ∂ξ)=_ at he
    rw [he]
    split_ifs with hl
    · have hgrad (x : X) : HasGradientAt (P.hyperobjective P.canonicalResponse)
          (gradient (P.hyperobjective P.canonicalResponse) x) x := by
        rw [P.gradient_hyperobjective P.canonicalResponse x]
        exact P.hasGradient_hyperobjective P.canonicalResponse x
      have hz := Descent.zero_query_threshold (P.hyperobjective P.canonicalResponse) x₀
        (gradient (P.hyperobjective P.canonicalResponse) x₀) Λ lower ε hΛ hε.le
        (InnerContraction.smooth_upper_model _ _ _ hgrad hlip x₀) hlower
        (hgap.trans ((le_div_iff₀ (by positivity : 0<2*Λ)).mpr (by nlinarith)))
      exact ENNReal.ofReal_le_ofReal hz
    · rw [selected_loss_integral O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit h
        (fun x => ‖gradient (P.hyperobjective P.canonicalResponse) x‖) hloss]
      have ha := PolishedFrozenUpper.accuracy O P hfx hfy hgy hgx hΛ hΔ hε hlip hlower x₀ yinit hgap hinit h
      rw [←ofReal_integral_eq_lintegral_ofReal ha.1 (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
      exact ENNReal.ofReal_le_ofReal ha.2
  constructor
  · exact (PolishedCompiledHistory.compiled_stopped_loss_le
      (Q:=of (X×Y)) (O:=of (FullResponse X Y)) (A:=of (Fin (outerCount Λ Δ ε))) (B:=of X) (H:=of History)
      (rawOracle O) q₀ o₀ c ξ h hfinite _ hloss).trans hrisk
  · exact (PolishedCompiledHistory.compiled_stopped_calls_le
      (Q:=of (X×Y)) (O:=of (FullResponse X Y)) (A:=of (Fin (outerCount Λ Δ ε))) (B:=of X) (H:=of History)
      (rawOracle O) q₀ o₀ c ξ h).trans hcost

end Bilevel.PolishedFrozenProcedure
