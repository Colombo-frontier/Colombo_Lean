import NCConcave16991.AcceleratedOuterTrajectory
import NCConcave16991.FiniteEvents

/-! # Actual three-quarters success of the accelerated outer algorithm -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.Accelerated

variable (p : ProblemParameters) [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def outerHistoryLaw : Measure (OuterHistory p) :=
  FiniteProcess.law (proxLaw p (gapCap p) (dualRegularization p) (outerTolerance p) (stageFailure p))
    (outerHorizon p)

instance outerHistoryLaw_probability : IsProbabilityMeasure (outerHistoryLaw p) :=
  FiniteProcess.law_probability _ _

def outerOutputLaw : Measure (OuterHistory p × Fin (outerHorizon p)) :=
  (outerHistoryLaw p).prod (uniformIndexLaw (outerHorizon p))

instance outerOutputLaw_probability : IsProbabilityMeasure (outerOutputLaw p) := by
  unfold outerOutputLaw
  infer_instance

variable {p} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

def outerOutput (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (ω : OuterHistory p × Fin (outerHorizon p)) : PrimalSpace dx :=
  checkedPath P hAS y0 hy0 ω.1 ω.2

theorem outer_public_failure_bound (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (outerHistoryLaw p).real {h | FiniteProcess.everBad (publicBad P hAS y0 hy0) (outerHorizon p) h} ≤
      1 / 12 := by
  have hh := outer_failure_probability P hAS (gapCap p) (dualRegularization_pos p)
    (dualRegularization_le_L p) (outerTolerance_pos p) (stageFailure_pos p) y0 hy0 (outerHorizon p)
  rw [show (horizon (dualRegularization p) p.diameter (outerTolerance p) : ℝ) = dualHorizon p from rfl,
    totalFailure_budget] at hh
  exact hh

/-- Conditioned on a fully successful realized history, the actual uniform
output has gradient failure at most 1/6, derived from actual prox descent. -/
theorem outer_good_uniform_failure (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (h : OuterHistory p)
    (hgood : ¬FiniteProcess.everBad (publicBad P hAS y0 hy0) (outerHorizon p) h) :
    (uniformIndexLaw (outerHorizon p)).real
      {i | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 (h, i))‖} ≤
        1 / 6 := by
  let x := checkedPath P hAS y0 hy0 h
  let q := checkedProxPath P hAS y0 hy0 h
  have hb := checkedPath_bounds P hAS y0 hy0 h hgood
  have hsize : 96 * (p.L * p.gap / p.epsilon ^ 2) ≤ (outerHorizon p : ℝ) := by
    have hs := (outerHorizon_bounds p).2.1
    dsimp [dimensionlessA] at hs
    linarith only [hs]
  have hlow : sInf (range (primalObjective K P.component)) ≤
      primalObjective K P.component (x (outerHorizon p)) :=
    csInf_le P.value_bddBelow (mem_range_self _)
  have hgap : primalObjective K P.component (x 0) -
      sInf (range (primalObjective K P.component)) ≤ p.gap := by
    simpa only [x, checkedPath_zero] using P.initial_gap
  have hm := inexact_proximal_uniform_failure (primalObjective K P.component) x q
    p.L_pos p.gap_pos.le p.epsilon_pos (fun t ↦ (hb t).1) (fun t ↦ (hb t).2) hlow hgap hsize
  have he : {i : Fin (outerHorizon p) | p.epsilon ≤ ‖(2 * p.L) • (x i - q i)‖} =
      {i | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 (h, i))‖} := by
    ext i
    have hg := P.moreau_hasGradientAt hAS (x i)
    change (p.epsilon ≤ ‖(2 * p.L) • (x i - q i)‖) ↔
      p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (x i)‖
    have hq : q i = proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow (x i) := by
      dsimp [q, checkedProxPath]
      rw [ite_eq_left i.isLt]
    rw [hq, hg.gradient]
  rw [he] at hm
  exact hm

/-- The actual failure event is bounded by independent uniform selection and
adaptive residual-check failures. Every bound is instantiated with public parameters. -/
theorem outer_gradient_failure_probability (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (outerOutputLaw p).real
      {ω | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 ω)‖} ≤
        1 / 4 := by
  classical
  let E := {ω : OuterHistory p × Fin (outerHorizon p) |
    p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 ω)‖}
  have hp (h : OuterHistory p) :
      (uniformIndexLaw (outerHorizon p)).real {i | (h, i) ∈ E} ≤
        1 / 6 + FiniteProcess.failureIndicator (publicBad P hAS y0 hy0) (outerHorizon p) h := by
    change (uniformIndexLaw (outerHorizon p)).real
      {i | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 (h, i))‖} ≤ _
    by_cases hb : FiniteProcess.everBad (publicBad P hAS y0 hy0) (outerHorizon p) h
    · have hu : (uniformIndexLaw (outerHorizon p)).real
          {i | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 (h, i))‖} ≤ 1 := by
        exact (measureReal_mono (subset_univ _) (measure_ne_top _ _)).trans_eq probReal_univ
      simp only [FiniteProcess.failureIndicator, hb, ↓reduceIte]
      linarith only [hu]
    · have hh := outer_good_uniform_failure P hAS y0 hy0 h hb
      simpa only [FiniteProcess.failureIndicator, hb, ↓reduceIte, add_zero] using hh
  have hh := integral_mono (μ := outerHistoryLaw p) Integrable.of_finite Integrable.of_finite hp
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const, probReal_univ, one_smul] at hh
  have hi := FiniteProcess.failureIndicator_integral
    (proxLaw p (gapCap p) (dualRegularization p) (outerTolerance p) (stageFailure p))
    (publicBad P hAS y0 hy0) (outerHorizon p)
  change (∫ h, FiniteProcess.failureIndicator (publicBad P hAS y0 hy0) (outerHorizon p) h
    ∂outerHistoryLaw p) = (outerHistoryLaw p).real
      {h | FiniteProcess.everBad (publicBad P hAS y0 hy0) (outerHorizon p) h} at hi
  rw [hi] at hh
  have hcheck := outer_public_failure_bound P hAS y0 hy0
  have he := product_event_probability (outerHistoryLaw p) (uniformIndexLaw (outerHorizon p)) E
  change (outerOutputLaw p).real E = _ at he
  rw [he]
  linarith only [hh, hcheck]

theorem outer_stationarity_probability (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (3 / 4 : ℝ) ≤ (outerOutputLaw p).real {ω | StationaryOutput P (outerOutput P hAS y0 hy0 ω)} := by
  have hf := outer_gradient_failure_probability P hAS y0 hy0
  have hc := measureReal_compl (μ := outerOutputLaw p)
    ((Set.to_countable {ω | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P)
      (outerOutput P hAS y0 hy0 ω)‖}).measurableSet)
  have he : {ω | p.epsilon ≤ ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 ω)‖}ᶜ =
      {ω | ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 ω)‖ < p.epsilon} := by
    ext ω
    simp
  rw [he, probReal_univ] at hc
  have hg : (3 / 4 : ℝ) ≤ (outerOutputLaw p).real
      {ω | ‖gradient (problemMoreauEnvelope P) (outerOutput P hAS y0 hy0 ω)‖ < p.epsilon} := by linarith
  apply hg.trans
  apply measureReal_mono
  · intro ω hω
    have hd := P.moreau_hasGradientAt hAS (outerOutput P hAS y0 hy0 ω)
    refine ⟨_, hd, ?_⟩
    rw [← hd.gradient]
    exact le_of_lt hω
  · exact measure_ne_top _ _

end NCConcave16991.Accelerated
