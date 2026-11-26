import Bilevel.PrimitiveQueryUpperSolver
import Bilevel.PrimitiveQueryUpperAssembly
import Bilevel.OracleSelectedIntegrals

/-! Actual expected-risk and original-call upper bounds in the stationary
fresh-law `PrimitiveQuery` model. The solver is the public causal program
constructed from numerical budgets, before the hidden instance is chosen.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry BorelAdaptive OracleCode Stateful
open CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

def Instance.fullKernel : Kernel (G.X × G.Y) (FullResponse G.X G.Y) :=
  I.historySFO.law.comap (fun q => (q,())) (measurable_id.prodMk measurable_const)

instance Instance.fullKernel_markov : IsMarkovKernel I.fullKernel := by
  unfold Instance.fullKernel
  infer_instance

theorem Instance.fullKernel_apply (q : G.X × G.Y) :
    I.fullKernel q=I.law.map (I.fullResponse q) := by
  rw [Instance.fullKernel,Kernel.comap_apply,I.historySFO_law]

theorem Instance.loss_measurable : Measurable I.loss :=
  (I.primitive.gradient_hyperobjective_lipschitz I.response).continuous.measurable.norm

theorem Instance.public_risk_eq (ε : ℝ) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    I.risk (publicAlgorithm G μ L ρ Δ ε R₀ σf σg)=
      ∫⁻ z,ENNReal.ofReal (I.loss (CachedUpper.output Λ Δ ε (0:G.X) z))
        ∂StochasticOuter.outputLaw (outerCount Λ Δ ε)
          ((CachedUpper.algorithm I.historySFO μ L L L ρ Λ Δ ε R₀ (0:G.X) (0:G.Y)).law ((),())) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := publicMachine G μ L ρ Δ ε R₀ σf σg
  have hexec (z : Fin (outerCount Λ Δ ε) × IndependentStream.Stream I.Seed) :
      seededStopped (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).program I.reply
        (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).start ((),z)=
      seededStopped m.program (fun _ : Unit => I.fullResponse) m.start ((),z) :=
    channel_seededStopped m.program (fun q => pack q.1 q.2)
      (decode (X:=G.X) (Y:=G.Y)) packLinear.continuous.measurable decode_measurable
      (fun _ : Unit => I.fullResponse) I.reply (fun _ _ _ => rfl) m.start ((),z)
  change (∫⁻ z,ENNReal.ofReal (I.loss
    (seededStopped (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).program I.reply
      (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).start ((),z)).2)
    ∂(StochasticOuter.uniformLaw (outerCount Λ Δ ε)).prod (IndependentStream.law I.law))=_
  simp_rw [hexec]
  have hs := selected_stopped_lintegral
    (Q:=of (G.X × G.Y)) (O:=of (FullResponse G.X G.Y))
    (I:=of (Fin (outerCount Λ Δ ε))) (B:=of (CachedOuterProcedure.State G.X G.Y)) (C:=of G.X)
    I.fullResponse (0,0) (0,0)
    (CachedOracleCode.algorithm (X:=G.X) (Y:=G.Y) μ L L L ρ σf σg Λ Δ ε R₀ (0:G.X) (0:G.Y))
    (CachedOracleCode.selected Λ Δ ε (0:G.X)) (CachedOracleCode.selected_measurable Λ Δ ε (0:G.X))
    (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) I.law I.fullResponse_measurable
    I.fullKernel I.fullKernel_apply (fun x => ENNReal.ofReal (I.loss x)) I.loss_measurable.ennreal_ofReal
  rw [CachedOracleCode.denote_algorithm I.historySFO I.fullKernel (fun _ => rfl)] at hs
  exact hs

theorem Instance.public_cost_eq (ε : ℝ) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    I.cost (publicAlgorithm G μ L ρ Δ ε R₀ σf σg)=
      ∫⁻ z,(z.2.2:ℝ≥0∞)
        ∂(CachedUpper.algorithm I.historySFO μ L L L ρ Λ Δ ε R₀ (0:G.X) (0:G.Y)).law ((),()) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := publicMachine G μ L ρ Δ ε R₀ σf σg
  have hexec (z : Fin (outerCount Λ Δ ε) × IndependentStream.Stream I.Seed) :
      seededCalls (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).program I.reply
        (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).start ((),z)=
      seededCalls m.program (fun _ : Unit => I.fullResponse) m.start ((),z) :=
    channel_seededCalls m.program (fun q => pack q.1 q.2)
      (decode (X:=G.X) (Y:=G.Y)) packLinear.continuous.measurable decode_measurable
      (fun _ : Unit => I.fullResponse) I.reply (fun _ _ _ => rfl) m.start ((),z)
  change (∫⁻ z,seededCalls (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).program I.reply
      (publicAlgorithm G μ L ρ Δ ε R₀ σf σg).start ((),z)
    ∂(StochasticOuter.uniformLaw (outerCount Λ Δ ε)).prod (IndependentStream.law I.law))=_
  simp_rw [hexec]
  have hs := selected_calls_lintegral
    (Q:=of (G.X × G.Y)) (O:=of (FullResponse G.X G.Y))
    (I:=of (Fin (outerCount Λ Δ ε))) (B:=of (CachedOuterProcedure.State G.X G.Y)) (C:=of G.X)
    I.fullResponse (0,0) (0,0)
    (CachedOracleCode.algorithm (X:=G.X) (Y:=G.Y) μ L L L ρ σf σg Λ Δ ε R₀ (0:G.X) (0:G.Y))
    (CachedOracleCode.selected Λ Δ ε (0:G.X)) (CachedOracleCode.selected_measurable Λ Δ ε (0:G.X))
    (StochasticOuter.uniformLaw (outerCount Λ Δ ε)) I.law I.fullResponse_measurable
    I.fullKernel I.fullKernel_apply
  rw [CachedOracleCode.denote_algorithm I.historySFO I.fullKernel (fun _ => rfl)] at hs
  exact hs

theorem Instance.public_normalized_upper {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    I.risk (publicAlgorithm G μ L ρ Δ ε R₀ σf σg)≤ENNReal.ofReal ε ∧
    I.cost (publicAlgorithm G μ L ρ Δ ε R₀ σf σg)≤
      ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  have hc := CachedUpper.normalized_upper I.primitive I.historySFO
    (fun x y => I.historySFO_fx_truth (x,y)) (fun x y => I.historySFO_fy_truth (x,y))
    (fun x y => I.historySFO_gy_truth (x,y)) (fun x y => I.historySFO_gx_truth (x,y))
    hL hΔ hε le_rfl le_rfl le_rfl hκ I.canonical_lower_bound
    (0:G.X) (0:G.Y) I.canonical_gap I.canonical_initialization ()
  dsimp only at hc
  constructor
  · rw [I.public_risk_eq ε]
    simp_rw [I.loss_eq_canonical]
    rw [← ofReal_integral_eq_lintegral_ofReal hc.1
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hc.2.1
  · rw [I.public_cost_eq ε]
    have he := ofReal_integral_eq_lintegral_ofReal hc.2.2.2.1
      (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    simp only [ENNReal.ofReal_natCast] at he
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hc.2.2.2.2

theorem Instance.public_three_term_upper {ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hθ : 1≤ρ/μ) (hκ : 1≤L/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    I.risk (publicAlgorithm G μ L ρ Δ ε R₀ σf σg)≤ENNReal.ofReal ε ∧
    I.cost (publicAlgorithm G μ L ρ Δ ε R₀ σf σg)≤
      ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) := by
  have hc := I.public_normalized_upper hL hΔ.le hε hκ
  exact ⟨hc.1,hc.2.trans (ENNReal.ofReal_le_ofReal
    (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))⟩

/-- Any subclass of the stationary fresh original-SFO model has this upper
bound, witnessed by the same solver, independent of every hidden instance. -/
theorem normalized_complexity_upper (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  apply complexity_le_of_solver C ε (fun G => publicAlgorithm G μ L ρ Δ ε R₀ σf σg)
  · intro G I _
    exact (I.public_normalized_upper hL hΔ hε hκ).1
  · intro G I _
    exact (I.public_normalized_upper hL hΔ hε hκ).2

/-- D+U+G minimax upper bound with the executed confidence and initialization
logarithms retained explicitly. The same public solver works for all instances. -/
theorem three_term_complexity_upper (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hθ : 1≤ρ/μ) (hκ : 1≤L/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) := by
  exact (normalized_complexity_upper C hL hΔ.le hε hκ).trans
    (ENNReal.ofReal_le_ofReal
      (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))

end Bilevel.PrimitiveQuery
