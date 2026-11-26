import Bilevel.PolishedHistorySourceFrozenGeneral

/-! The public all-accuracy dispatch on the original conditional-moment
probability space. In the large-accuracy branch the actual machine halts
without a call; otherwise the literal cached query body is executed. The
terminal uniform index is sampled independently after this public body. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful OracleCode CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {G : Geometry} {μ Lf Lg Cf ρ Δ R₀ σf σg Λ ε : ℝ}

open Classical in
def sourceFrozenDispatchMachine (G : Geometry) (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (x₀ : G.X) (yinit : G.Y) :=
  if 2*Λ*Δ≤ε^2 then
    compile ((0:G.X),(0:G.Y)) ((0:G.X × G.Y),(0:G.X × G.Y))
      (Code.pure (Q:=of (G.X × G.Y)) (O:=of (FullResponse G.X G.Y))
        (A:=of Unit) (B:=of (CachedOuterProcedure.State G.X G.Y))
        (fun _ => CachedOuterProcedure.initialState x₀) measurable_const)
  else sourceFrozenGeneralMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit

open Classical in
def sourceFrozenDispatchSelect (Λ Δ ε : ℝ) (x₀ : G.X)
    (z : Fin (outerCount Λ Δ ε) × CachedOuterProcedure.State G.X G.Y) : G.X :=
  if 2*Λ*Δ≤ε^2 then x₀ else CachedOracleCode.selected Λ Δ ε x₀ z

/-- One actual public machine and its actual source-probability output obey
both accuracy and original-call bounds on every positive accuracy range. -/
theorem source_frozen_general_dispatch_upper
    (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ Lf Lg Cf ρ)
    (x₀ : G.X) (yinit : G.Y) (lower : ℝ)
    (E : SourceExperiment (sourceFrozenDispatchMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit).program
      (generalPrimitiveUpper P) (generalPrimitiveLower P) (rawReadUpper G) (rawReadLower G) σf σg)
    (hstart : E.initial=(sourceFrozenDispatchMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit).start ())
    (hΛ : 0<Λ) (hLaΛ : anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε)
    (hlip : ∀ x y,‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖≤Λ*‖x-y‖)
    (hlower : ∀ x,lower≤P.hyperobjective P.canonicalResponse x)
    (hgap : P.hyperobjective P.canonicalResponse x₀-lower≤Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖≤R₀) :
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ z,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse)
      (sourceFrozenDispatchSelect Λ Δ ε x₀
        (z.1,HistoryProgram.stoppedOutput
          (sourceFrozenDispatchMachine G μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit).program
          (experimentPath E.state z.2)))‖)
      ∂(StochasticOuter.uniformLaw (outerCount Λ Δ ε)).prod E.law)≤ENNReal.ofReal ε ∧
    E.actualCost≤ENNReal.ofReal (CachedUpper.rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) ∧
    (2*Λ*Δ≤ε^2 → E.actualCost=0) := by
  classical
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  by_cases hl : 2*Λ*Δ≤ε^2
  · revert hstart
    revert E
    simp only [sourceFrozenDispatchMachine]
    rw [if_pos hl]
    intro E hstart
    have htf := generalPrimitiveUpper_measurable P
    have htg := generalPrimitiveLower_measurable P
    have hrf := rawReadUpper_measurable G
    have hrg := rawReadLower_measurable G
    let fallback := exactRawResponse G (tf:=generalPrimitiveUpper P) (tg:=generalPrimitiveLower P)
    have hf := exactRawResponse_measurable G htf htg
    have hcost := SourceExperiment.compiled_cost_le_denote
      (Q:=of (G.X × G.Y)) (O:=of (FullResponse G.X G.Y))
      (Inp:=of Unit) (B:=of (CachedOuterProcedure.State G.X G.Y))
      ((0:G.X),(0:G.Y)) ((0:G.X × G.Y),(0:G.X × G.Y))
      (Code.pure (fun _ => CachedOuterProcedure.initialState x₀) measurable_const)
      E htf htg hrf hrg fallback hf (fun _ => rfl) (fun _ => rfl) () hstart
    simp only [OracleCode.History.denote,Procedure.pure_law] at hcost
    have hc : E.actualCost=0 := by
      rw [lintegral_dirac'] at hcost
      · exact le_antisymm (by simpa using hcost) (zero_le E.actualCost)
      · exact (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
          (measurable_snd.comp measurable_snd)
    have hgrad (x : G.X) : HasGradientAt (P.hyperobjective P.canonicalResponse)
        (gradient (P.hyperobjective P.canonicalResponse) x) x := by
      rw [P.gradient_hyperobjective P.canonicalResponse x]
      exact P.hasGradient_hyperobjective P.canonicalResponse x
    have hz := Descent.zero_query_threshold (P.hyperobjective P.canonicalResponse) x₀
      (gradient (P.hyperobjective P.canonicalResponse) x₀) Λ lower ε hΛ hε.le
      (InnerContraction.smooth_upper_model _ _ _ hgrad hlip x₀) hlower
      (hgap.trans ((le_div_iff₀ (by positivity : 0<2*Λ)).mpr (by nlinarith)))
    constructor
    · simpa only [sourceFrozenDispatchSelect,if_pos hl,lintegral_const,measure_univ,mul_one]
        using ENNReal.ofReal_le_ofReal hz
    · exact ⟨by rw [hc]; exact zero_le _,fun _ => hc⟩
  · revert hstart
    revert E
    simp only [sourceFrozenDispatchMachine]
    rw [if_neg hl]
    intro E hstart
    have h := source_frozen_general_upper P x₀ yinit lower E hstart hΛ hLaΛ hΔ hε hlip hlower hgap hinit
    exact ⟨by simpa only [sourceFrozenDispatchSelect,if_neg hl] using h.1,h.2,fun hbad => (hl hbad).elim⟩

end Bilevel.PolishedHistory
