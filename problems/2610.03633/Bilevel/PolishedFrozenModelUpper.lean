import Bilevel.PolishedFrozenModelUpperRaw
import Bilevel.PolishedHistoryUpperTheorem

/-! The literal frozen algorithm, including its zero-query branch, as one
common solver in the manuscript's arbitrary-history paired-kernel model. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery BorelAdaptive OracleCode Stateful
open CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {μ L ρ Δ R₀ σf σg : ℝ}

def sourceFrozenMachineAt (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ) (x₀ : G.X) (yinit : G.Y) :
    Machine (of (G.X×G.Y)) (of (FullResponse G.X G.Y))
      (of (Fin (outerCount (CachedUpper.universalCurvature L μ L L L ρ) Δ ε))) (of G.X) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  exact compile (0,0) (0,0)
    (PolishedFrozenCode.sourceSelectedAlgorithm (X:=G.X) (Y:=G.Y)
      μ L L L ρ σf σg Λ Δ ε R₀ x₀ yinit)

def sourceFrozenAlgorithmAt (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ)
    (x₀ : G.X) (yinit : G.Y) : Algorithm G := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := sourceFrozenMachineAt G μ L ρ Δ ε R₀ σf σg x₀ yinit
  exact {
    Private := Fin (outerCount Λ Δ ε)
    State := m.state
    privateLaw := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
    program := channelProgram m.program (fun q => pack q.1 q.2)
      (PrimitiveQuery.decode (X:=G.X) (Y:=G.Y)) packLinear.continuous.measurable decode_measurable
    start := m.start
    start_measurable := m.start_measurable }

variable {G : Geometry} (I : Instance G μ L ρ Δ R₀ σf σg)

/-- Actual stopped expected gradient and sharp logarithmic call budget for
the named frozen algorithm, on every positive accuracy range. Its code
includes public zero-call dispatch, cached y0 reuse, and immediate abort. -/
theorem Instance.source_frozen_normalized_upper {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    I.risk (sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤ENNReal.ofReal ε ∧
    I.cost (sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤
      ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := sourceFrozenMachineAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit
  let ξ := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
  have hΛ : 0<Λ := hL.trans_le (le_max_left _ _)
  have hcurv : (1+L/μ)^2*(L+ρ*L/μ)≤Λ := le_max_right _ _
  have hLaΛ : anchorSmoothness L (L/μ)≤Λ := by
    have hh : 0≤(1+L/μ)^2*(ρ*L/μ) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg I.primitive.ρ_nonneg I.primitive.Cf_nonneg) I.primitive.μ_pos.le)
    unfold anchorSmoothness
    nlinarith
  have hlip (x y : G.X) : ‖gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) x-
      gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) y‖≤Λ*‖x-y‖ :=
    (I.primitive.gradient_hyperobjective_norm_sub_le I.primitive.canonicalResponse x y).trans
      (mul_le_mul_of_nonneg_right hcurv (norm_nonneg _))
  have hc := PolishedFrozenProcedure.source_compiled_accuracy_and_cost I.oracle I.primitive
    I.truth_fx I.truth_fy I.truth_gy I.truth_gx hΛ hΔ hε hLaΛ hlip
    I.upper_canonical_lower_bound I.x₀ I.yinit I.upper_canonical_gap I.upper_canonical_initialization
    I.initialHistory (0,0) (0,0)
  have hrate := CachedUpper.cost_le_rateBound (Cf:=L) (σf:=σf) (σg:=σg) (R₀:=R₀)
    I.primitive.μ_pos I.primitive.strong_convexity_le_smoothness I.primitive.Lf_nonneg
    I.primitive.ρ_nonneg hΛ hLaΛ hΔ hε
  have hnorm := CachedUpper.rateBound_le_normalized (σf:=σf) (σg:=σg) (ε:=ε) (R₀:=R₀)
    I.primitive.μ_pos hL I.primitive.Lf_nonneg I.primitive.Lg_nonneg I.primitive.Cf_nonneg
    I.primitive.ρ_nonneg le_rfl le_rfl le_rfl hκ hΔ
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
    exact hc.2.trans (ENNReal.ofReal_le_ofReal (hrate.trans hnorm))

/-- The named source algorithm makes zero original calls in its stated
large-accuracy regime, in the same arbitrary-history experiment. -/
theorem Instance.source_frozen_zero_calls (ε : ℝ)
    (hlarge : 2*CachedUpper.universalCurvature L μ L L L ρ*Δ≤ε^2) :
    I.cost (sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)=0 := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := sourceFrozenMachineAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit
  let ξ := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
  change (∫⁻ w,HistoryProgram.totalCalls m.program w
    ∂HistoryProgram.trajectoryLaw (channelProgram m.program (fun q => pack q.1 q.2)
      PrimitiveQuery.decode packLinear.continuous.measurable decode_measurable)
      I.historyOracle ξ m.start I.initialHistory)=0
  rw [I.packed_trajectoryLaw m.program ξ m.start]
  exact PolishedFrozenProcedure.source_compiled_zero_calls I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit
    I.initialHistory hlarge (0,0) (0,0)

theorem Instance.source_frozen_three_term_upper {ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hθ : 1≤ρ/μ) (hκ : 1≤L/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    I.risk (sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤ENNReal.ofReal ε ∧
    I.cost (sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤
      ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) := by
  have hc := I.source_frozen_normalized_upper hL hΔ.le hε hκ
  exact ⟨hc.1,hc.2.trans (ENNReal.ofReal_le_ofReal
    (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))⟩

/-- The same named source algorithm supplies the minimax upper witness for
any subclass of the full history-dependent paired original-SFO model. -/
theorem source_frozen_normalized_complexity_upper (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  apply complexity_le_of_solver C ε (fun G x y => sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg x y)
  · intro G I _
    exact (I.source_frozen_normalized_upper hL hΔ hε hκ).1
  · intro G I _
    exact (I.source_frozen_normalized_upper hL hΔ hε hκ).2

/-- The zero-query regime is exactly zero minimax complexity, with the
same common public solver and actual stopped-call definition. -/
theorem source_frozen_zero_complexity (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ)
    (hlarge : 2*CachedUpper.universalCurvature L μ L L L ρ*Δ≤ε^2) : Complexity C ε=0 := by
  apply le_antisymm _ (zero_le _)
  apply complexity_le_of_solver C ε (fun G x y => sourceFrozenAlgorithmAt G μ L ρ Δ ε R₀ σf σg x y)
  · intro G I _
    exact (I.source_frozen_normalized_upper hL hΔ hε hκ).1
  · intro G I _
    exact (I.source_frozen_zero_calls ε hlarge).le

theorem source_frozen_three_term_complexity_upper (C : InstanceClass μ L ρ Δ R₀ σf σg) {ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε) (hθ : 1≤ρ/μ) (hκ : 1≤L/μ)
    (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    Complexity C ε≤ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) := by
  exact (source_frozen_normalized_complexity_upper C hL hΔ.le hε hκ).trans
    (ENNReal.ofReal_le_ofReal
      (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))

end Bilevel.PolishedHistory
