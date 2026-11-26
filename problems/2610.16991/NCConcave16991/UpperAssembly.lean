import NCConcave16991.ProblemAnalysis
import NCConcave16991.OracleMeasurability
import NCConcave16991.OracleResponseMeasurability
import NCConcave16991.UpperProbability
import NCConcave16991.TheoremStatements

/-! # Probability guarantees in the actual randomized oracle model -/

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991

noncomputable section

theorem randomizedOutput_measurable {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter}
    (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (h : P.averagedSmooth) (budget : ℕ) :
    @Measurable A.Seed (PrimalSpace dx) A.seedSpace inferInstance
      (randomizedOutput A P budget) := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  exact OraclePolicy.output_measurable K A.policy (oracleResponse_measurable P h) budget

theorem stationarity_event_measurable {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter}
    (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (h : P.averagedSmooth) (budget : ℕ) :
    @MeasurableSet A.Seed A.seedSpace
      {seed | StationaryOutput P (randomizedOutput A P budget seed)} := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  have hg := (P.moreau_gradient_continuous h).measurable.comp
    (randomizedOutput_measurable A P h budget)
  have he : {seed | StationaryOutput P (randomizedOutput A P budget seed)} =
      {seed | ‖gradient (problemMoreauEnvelope P) (randomizedOutput A P budget seed)‖ ≤ p.epsilon} := by
    ext seed
    exact P.stationaryOutput_iff h _
  rw [he]
  exact measurableSet_le hg.norm measurable_const

/-- A genuine expected-square guarantee implies the actual success event in
the unrestricted measurable policy model, with the same fixed query budget. -/
theorem squaredExpectation_implies_success {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter}
    (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (h : P.averagedSmooth) (budget : ℕ)
    (hmean : SquaredExpectationGuarantee A P budget) : Success A P budget := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  obtain ⟨hdiff, hint, hmean⟩ := hmean
  let g := fun seed ↦ gradient (problemMoreauEnvelope P) (randomizedOutput A P budget seed)
  have hg : Measurable g := (P.moreau_gradient_continuous h).measurable.comp
    (randomizedOutput_measurable A P h budget)
  have hp := stationarity_two_thirds A.law hg.norm (fun seed ↦ norm_nonneg (g seed))
    hint p.epsilon_pos hmean
  have hsub : {seed | ‖g seed‖ < p.epsilon} ⊆
      {seed | StationaryOutput P (randomizedOutput A P budget seed)} := by
    intro seed hs
    exact (P.stationaryOutput_iff h _).2 (le_of_lt hs)
  have hre : (2 / 3 : ℝ) ≤ A.law.real
      {seed | StationaryOutput P (randomizedOutput A P budget seed)} :=
    hp.trans (measureReal_mono hsub)
  refine ⟨stationarity_event_measurable A P h budget, ?_⟩
  have he := (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top A.law {seed | StationaryOutput P (randomizedOutput A P budget seed)})).2 hre
  norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] at he
  exact he

theorem validBudget_of_squaredExpectation {p : ProblemParameters} {budget : ℕ}
    (h : ValidSquaredExpectationBudget p budget) : ValidBudget p .averaged budget := by
  intro dx dy K x0
  obtain ⟨A, hA⟩ := h dx dy K x0
  refine ⟨A, fun P h0 hP ↦ squaredExpectation_implies_success A P hP budget (hA P h0 hP)⟩

theorem validBudget_of_threeQuarters {p : ProblemParameters} {budget : ℕ}
    (h : ValidThreeQuartersBudget p budget) : ValidBudget p .averaged budget := by
  intro dx dy K x0
  obtain ⟨A, hA⟩ := h dx dy K x0
  refine ⟨A, fun P h0 hP ↦ ?_⟩
  obtain ⟨hm, hp⟩ := hA P h0 hP
  refine ⟨hm, le_trans ?_ hp⟩
  have he := ENNReal.ofReal_le_ofReal (by norm_num : (2 / 3 : ℝ) ≤ 3 / 4)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat] using he

end

end NCConcave16991
