import Bilevel.PolishedHistorySourceSFO
import Bilevel.CachedOracleHistoryAlgorithm
import Bilevel.ChiUpperTheorem

/-! Source probability-space upper theorem for the actual cached query
body. Its queries have fixed public initialization and all private
randomness is a fresh independent uniform terminal output index. Original
conditional-moment admissibility is transported through a constructed RCD;
no final accuracy or complexity bound is an admissibility field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful OracleCode CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg ε : ℝ}

def primitiveUpper (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ)
    (q : G.X × G.Y) : G.Query := pack (P.fx q.1 q.2) (P.fy q.1 q.2)

def primitiveLower (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ)
    (q : G.X × G.Y) : G.Query := pack (P.gx q.1 q.2) (P.gy q.1 q.2)

theorem primitiveUpper_measurable (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ) :
    Measurable (primitiveUpper P) := by
  have hl : LipschitzWith ⟨L,P.Lf_nonneg⟩
      (fun q : G.Query => pack (P.fx q.1 q.2) (P.fy q.1 q.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simp only [dist_eq_norm,NNReal.coe_mk]
    exact (full_gradient_lipschitz_iff P.fx P.fy P.Lf_nonneg).mpr
      P.smooth_f q.1 q'.1 q.2 q'.2
  exact hl.continuous.measurable.comp packLinear.continuous.measurable

theorem primitiveLower_measurable (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ) :
    Measurable (primitiveLower P) := by
  have hl : LipschitzWith ⟨L,P.Lg_nonneg⟩
      (fun q : G.Query => pack (P.gx q.1 q.2) (P.gy q.1 q.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simp only [dist_eq_norm,NNReal.coe_mk]
    exact (full_gradient_lipschitz_iff P.gx P.gy P.Lg_nonneg).mpr
      P.smooth_g q.1 q'.1 q.2 q'.2
  exact hl.continuous.measurable.comp packLinear.continuous.measurable

def sourceCachedBody (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ) (x₀ : G.X) (yinit : G.Y) :=
  CachedOracleCode.algorithm (X:=G.X) (Y:=G.Y) μ L L L ρ σf σg
    (CachedUpper.universalCurvature L μ L L L ρ) Δ ε R₀ x₀ yinit

def sourceCachedMachine (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ) (x₀ : G.X) (yinit : G.Y) :=
  compile (0,0) (0,0) (sourceCachedBody G μ L ρ Δ ε R₀ σf σg x₀ yinit)

/-- For every source-admissible probability-space execution of the cached
public query body, the actual independent-uniform terminal output has
expected gradient norm at most ε and actual original-call expectation at
most the explicit normalized budget, with both logarithms retained. -/
theorem source_cached_normalized_upper
    (P : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ)
    (x₀ : G.X) (yinit : G.Y) (lower : ℝ)
    (E : SourceExperiment (sourceCachedMachine G μ L ρ Δ ε R₀ σf σg x₀ yinit).program
      (primitiveUpper P) (primitiveLower P) (rawReadUpper G) (rawReadLower G) σf σg)
    (hstart : E.initial=(sourceCachedMachine G μ L ρ Δ ε R₀ σf σg x₀ yinit).start ())
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ)
    (hlower : ∀ x,lower≤P.hyperobjective P.canonicalResponse x)
    (hgap : P.hyperobjective P.canonicalResponse x₀-lower≤Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖≤R₀) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    (∫⁻ z,ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse)
      (CachedOracleCode.selected Λ Δ ε x₀
        (z.1,HistoryProgram.stoppedOutput
          (sourceCachedMachine G μ L ρ Δ ε R₀ σf σg x₀ yinit).program
          (experimentPath E.state z.2)))‖)
      ∂(StochasticOuter.uniformLaw (outerCount Λ Δ ε)).prod E.law)≤ENNReal.ofReal ε ∧
    E.actualCost≤ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let c := sourceCachedBody G μ L ρ Δ ε R₀ σf σg x₀ yinit
  let m := sourceCachedMachine G μ L ρ Δ ε R₀ σf σg x₀ yinit
  let htf := primitiveUpper_measurable P
  let htg := primitiveLower_measurable P
  let hrf := rawReadUpper_measurable G
  let hrg := rawReadLower_measurable G
  let fallback := exactRawResponse G (tf:=primitiveUpper P) (tg:=primitiveLower P)
  let hf := exactRawResponse_measurable G htf htg
  let O := E.fullSFO G htf htg
  let R := E.repairedOracle htf htg hrf hrg fallback hf
  let ν := (CachedUpper.algorithm O μ L L L ρ Λ Δ ε R₀ x₀ yinit).law ((),(E.initial,0))
  have hd : (OracleCode.History.denote (H:=of (m.state × ℕ)) R.law R.update R.update_measurable c).law
      ((),(E.initial,0))=ν := by
    change (OracleCode.History.denote (H:=of (m.state × ℕ)) O.law O.update O.update_measurable
      (CachedOracleCode.algorithm μ L L L ρ σf σg Λ Δ ε R₀ x₀ yinit)).law ((),(E.initial,0))=ν
    rw [CachedOracleCode.History.denote_algorithm]
  have hc := CachedUpper.normalized_upper P O
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    hL hΔ hε le_rfl le_rfl le_rfl hκ hlower x₀ yinit hgap hinit (E.initial,0)
  dsimp only at hc
  have hcnt := ofReal_integral_eq_lintegral_ofReal hc.2.2.2.1
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
  simp only [ENNReal.ofReal_natCast] at hcnt
  have hνfinite : (∫⁻ y,(y.2.2:ℝ≥0∞) ∂ν)≠⊤ := by
    rw [←hcnt]
    exact ENNReal.ofReal_ne_top
  have hdenfinite : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of (m.state × ℕ)) R.law R.update R.update_measurable c).law
        ((),(E.initial,0)))≠⊤ := by rw [hd];exact hνfinite
  have hcost := SourceExperiment.compiled_cost_le_denote
    (Q:=of (G.X × G.Y)) (O:=of (FullResponse G.X G.Y))
    (Inp:=of Unit) (B:=of (CachedOuterProcedure.State G.X G.Y))
    ((0:G.X),(0:G.Y)) ((0:G.X × G.Y),(0:G.X × G.Y)) c E htf htg hrf hrg fallback hf
    (fun _ => rfl) (fun _ => rfl) () hstart
  change E.actualCost≤∫⁻ y,(y.2.2:ℝ≥0∞)
    ∂(OracleCode.History.denote (H:=of (m.state × ℕ)) R.law R.update R.update_measurable c).law
      ((),(E.initial,0)) at hcost
  rw [hd] at hcost
  have hout := SourceExperiment.compiled_output_law
    (Q:=of (G.X × G.Y)) (O:=of (FullResponse G.X G.Y))
    (Inp:=of Unit) (B:=of (CachedOuterProcedure.State G.X G.Y))
    ((0:G.X),(0:G.Y)) ((0:G.X × G.Y),(0:G.X × G.Y)) c E htf htg hrf hrg fallback hf
    (fun _ => rfl) (fun _ => rfl) () hstart hdenfinite
  change E.law.map (fun ω => HistoryProgram.stoppedOutput m.program (experimentPath E.state ω))=
    ((OracleCode.History.denote (H:=of (m.state × ℕ)) R.law R.update R.update_measurable c).law
      ((),(E.initial,0))).map Prod.fst at hout
  rw [hd] at hout
  let sourceOut : E.Ω → CachedOuterProcedure.State G.X G.Y := fun ω =>
    HistoryProgram.stoppedOutput m.program (experimentPath E.state ω)
  have hsout : Measurable sourceOut :=
    (HistoryProgram.stoppedOutput_measurable m.program).comp
      (experimentPath_measurable E.state E.state_measurable)
  let select := CachedOracleCode.selected (Y:=G.Y) Λ Δ ε x₀
  have hs := CachedOracleCode.selected_measurable (Y:=G.Y) Λ Δ ε x₀
  have hlaw := independent_terminal_selection_law
    (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) E.law ν sourceOut Prod.fst
    hsout measurable_fst hout select hs
  let loss : G.X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖gradient (P.hyperobjective P.canonicalResponse) x‖)
  have hloss : Measurable loss :=
    (P.gradient_hyperobjective_lipschitz P.canonicalResponse).continuous.measurable.norm.ennreal_ofReal
  have hselSource : Measurable (fun z : Fin (outerCount Λ Δ ε) × E.Ω => select (z.1,sourceOut z.2)) :=
    hs.comp (measurable_fst.prodMk (hsout.comp measurable_snd))
  have hselKernel : Measurable (fun z : Fin (outerCount Λ Δ ε) × Outcome (CachedOuterProcedure.State G.X G.Y) (m.state × ℕ) =>
      select (z.1,z.2.1)) :=
    hs.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have he := congrArg (fun η : Measure G.X => ∫⁻ x,loss x ∂η) hlaw
  dsimp only at he
  rw [lintegral_map hloss hselSource,lintegral_map hloss hselKernel] at he
  constructor
  · refine he.trans_le ?_
    exact (ofReal_integral_eq_lintegral_ofReal hc.1
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm.le.trans
        (ENNReal.ofReal_le_ofReal hc.2.1)
  · exact hcost.trans (hcnt ▸ ENNReal.ofReal_le_ofReal hc.2.2.2.2)

end Bilevel.PolishedHistory
