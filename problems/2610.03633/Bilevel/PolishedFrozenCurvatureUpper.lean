import Bilevel.PolishedFrozenModelUpper
import Bilevel.CachedCurvatureUpper

/-! Supplied-curvature upper certificate for the literal frozen algorithm,
including its zero-call branch, in the actual common history model. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery BorelAdaptive OracleCode Stateful
open CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {μ L ρ Δ R₀ σf σg : ℝ}

def sourceControlledMachineAt (G : Geometry) (μ L ρ Δ ε R₀ σf σg Λcert : ℝ)
    (x₀ : G.X) (yinit : G.Y) :
    Machine (of (G.X×G.Y)) (of (FullResponse G.X G.Y))
      (of (Fin (outerCount (CachedUpper.controlledCurvature L μ L L Λcert) Δ ε))) (of G.X) := by
  let Λ := CachedUpper.controlledCurvature L μ L L Λcert
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  exact compile (0,0) (0,0)
    (PolishedFrozenCode.sourceSelectedAlgorithm (X:=G.X) (Y:=G.Y)
      μ L L L ρ σf σg Λ Δ ε R₀ x₀ yinit)

def sourceControlledAlgorithmAt (G : Geometry) (μ L ρ Δ ε R₀ σf σg Λcert : ℝ)
    (x₀ : G.X) (yinit : G.Y) : Algorithm G := by
  let Λ := CachedUpper.controlledCurvature L μ L L Λcert
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := sourceControlledMachineAt G μ L ρ Δ ε R₀ σf σg Λcert x₀ yinit
  exact {
    Private := Fin (outerCount Λ Δ ε)
    State := m.state
    privateLaw := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
    program := channelProgram m.program (fun q => pack q.1 q.2)
      (PrimitiveQuery.decode (X:=G.X) (Y:=G.Y)) packLinear.continuous.measurable decode_measurable
    start := m.start
    start_measurable := m.start_measurable }

variable {G : Geometry} (I : Instance G μ L ρ Δ R₀ σf σg)

theorem Instance.source_frozen_curvature_upper {ε Λcert C_F : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hκ : 1≤L/μ) (hθ : 1≤ρ/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤C_F*L*(L/μ)^2) (hlip : I.CurvatureBound Λcert) :
    let Λ := CachedUpper.controlledCurvature L μ L L Λcert
    I.risk (sourceControlledAlgorithmAt G μ L ρ Δ ε R₀ σf σg Λcert I.x₀ I.yinit)≤ENNReal.ofReal ε ∧
    I.cost (sourceControlledAlgorithmAt G μ L ρ Δ ε R₀ σf σg Λcert I.x₀ I.yinit)≤
      ENNReal.ofReal (CachedUpper.controlledThreeRateBound L μ L L L ρ σf σg Λ
        (CachedUpper.controlledConstant C_F) Δ ε R₀) := by
  let Λ := CachedUpper.controlledCurvature L μ L L Λcert
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := sourceControlledMachineAt G μ L ρ Δ ε R₀ σf σg Λcert I.x₀ I.yinit
  let ξ := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
  have hΛ : 0<Λ := hL.trans_le (le_max_left _ _)
  have hLaΛ : anchorSmoothness L (L/μ)≤Λ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hcertΛ : Λcert≤Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hfull (x y : G.X) :
      ‖gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) x-
        gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) y‖≤Λ*‖x-y‖ := by
    rw [I.upper_canonical_hyperobjective]
    exact (hlip x y).trans (mul_le_mul_of_nonneg_right hcertΛ (norm_nonneg _))
  have hparameters := CachedNormalizedRate.normalized_parameters I.primitive.μ_pos hL
    I.primitive.Lf_nonneg I.primitive.Lg_nonneg I.primitive.Cf_nonneg
    le_rfl le_rfl le_rfl (div_nonneg I.primitive.ρ_nonneg I.primitive.μ_pos.le) hκ
  have hΛb : Λ≤CachedUpper.controlledConstant C_F*L*(L/μ)^2 :=
    CachedUpper.controlled_curvature_budget hL.le hκ hcert hparameters.2.1
  have hc := PolishedFrozenProcedure.source_compiled_accuracy_and_cost I.oracle I.primitive
    I.truth_fx I.truth_fy I.truth_gy I.truth_gx hΛ hΔ.le hε hLaΛ hfull
    I.upper_canonical_lower_bound I.x₀ I.yinit I.upper_canonical_gap I.upper_canonical_initialization
    I.initialHistory (0,0) (0,0)
  have hrate := CachedUpper.cost_le_rateBound (Cf:=L) (σf:=σf) (σg:=σg) (R₀:=R₀)
    I.primitive.μ_pos I.primitive.strong_convexity_le_smoothness I.primitive.Lf_nonneg
    I.primitive.ρ_nonneg hΛ hLaΛ hΔ.le hε
  have hcontrolled := CachedUpper.rateBound_le_curvatureControlled (σf:=σf) (σg:=σg) (R₀:=R₀)
    I.primitive.μ_pos hL I.primitive.Lf_nonneg I.primitive.Lg_nonneg I.primitive.Cf_nonneg
    I.primitive.ρ_nonneg le_rfl le_rfl le_rfl hθ hκ hΔ hε haccuracy hΛb
  constructor
  · change (∫⁻ w,ENNReal.ofReal (I.loss (HistoryProgram.stoppedOutput m.program w))
      ∂HistoryProgram.trajectoryLaw (channelProgram m.program (fun q => pack q.1 q.2)
        PrimitiveQuery.decode packLinear.continuous.measurable decode_measurable)
        I.historyOracle ξ m.start I.initialHistory)≤_
    rw [I.packed_trajectoryLaw m.program ξ m.start]
    simpa only [I.upper_loss_eq_canonical] using hc.1
  · change (∫⁻ w,HistoryProgram.totalCalls m.program w
      ∂HistoryProgram.trajectoryLaw (channelProgram m.program (fun q => pack q.1 q.2)
        PrimitiveQuery.decode packLinear.continuous.measurable decode_measurable)
        I.historyOracle ξ m.start I.initialHistory)≤_
    rw [I.packed_trajectoryLaw m.program ξ m.start]
    exact hc.2.trans (ENNReal.ofReal_le_ofReal (hrate.trans hcontrolled))

theorem source_frozen_curvature_complexity_upper
    (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε Λcert C_F : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hκ : 1≤L/μ) (hθ : 1≤ρ/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hcert : Λcert≤C_F*L*(L/μ)^2)
    (hC : ∀ G I,C G I → I.CurvatureBound Λcert) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.controlledThreeRateBound L μ L L L ρ σf σg
      (CachedUpper.controlledCurvature L μ L L Λcert) (CachedUpper.controlledConstant C_F) Δ ε R₀) := by
  apply complexity_le_of_solver C ε
    (fun G x y => sourceControlledAlgorithmAt G μ L ρ Δ ε R₀ σf σg Λcert x y)
  · intro G I hI
    exact (I.source_frozen_curvature_upper hL hΔ hε hκ hθ haccuracy hcert (hC G I hI)).1
  · intro G I hI
    exact (I.source_frozen_curvature_upper hL hΔ hε hκ hθ haccuracy hcert (hC G I hI)).2

end Bilevel.PolishedHistory
