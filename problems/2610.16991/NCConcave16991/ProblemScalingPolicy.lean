import NCConcave16991.ProblemScalingMoreau
import NCConcave16991.OracleSimulation
import NCConcave16991.OracleProgramProbability
import NCConcave16991.UpperAssembly

/-! # Scaling preserves unrestricted randomized oracle budgets -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991.ProblemScaling

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  {a b : ℝ} {ha : 0 < a} {hb : 0 < b}

def sourceQuery (q : OracleQuery p.n dx (dualDomain K b hb)) : OracleQuery p.n dx K :=
  (q.1, b • q.2.1, ⟨b • q.2.2.val, q.2.2.property⟩)

def targetReply (_q : OracleQuery p.n dx (dualDomain K b hb))
    (r : OracleAnswer dx dy) : OracleAnswer dx dy :=
  (a * r.1, (a * b) • r.2.1, (a * b) • r.2.2)

theorem sourceQuery_measurable : Measurable
    (sourceQuery (p := p) (dx := dx) (K := K) (hb := hb)) := by
  apply measurable_fst.prodMk
  apply Measurable.prodMk
  · exact (continuous_const_smul b).measurable.comp (measurable_fst.comp measurable_snd)
  · apply Measurable.subtype_mk
    exact (continuous_const_smul b).measurable.comp
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))

theorem targetReply_measurable : Measurable
    (Function.uncurry (targetReply (p := p) (dx := dx) (K := K) (a := a) (hb := hb))) := by
  apply Measurable.prodMk
  · exact measurable_const.mul (measurable_fst.comp measurable_snd)
  · exact ((continuous_const_smul (a * b)).measurable.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
      ((continuous_const_smul (a * b)).measurable.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem exact_reply (P : Problem p dx dy K) (ha : 0 < a) (hb : 0 < b)
    (q : OracleQuery p.n dx (dualDomain K b hb)) :
    oracleResponse (toProblem P ha hb) q =
      targetReply (a := a) q (oracleResponse P (sourceQuery q)) := rfl

variable {Ω : Type*} [MeasurableSpace Ω]

def simulationProgram
    (A : OraclePolicy.AdaptivePolicy (dualDomain K b hb) (n := p.n) (dx := dx) Ω)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ) :
    OracleProgram.ProblemProgram K (n := p.n) (dx := dx) Ω T :=
  OracleProgram.map
    (OracleSimulation.program (dualDomain K b hb) A (⟨0, p.n_pos⟩, x0, ⟨y0, hy0⟩)
      sourceQuery (targetReply (a := a)) sourceQuery_measurable targetReply_measurable T)
    (fun x ↦ b • x) (continuous_const_smul b).measurable

theorem eval_simulationProgram (P : Problem p dx dy K) (ha : 0 < a) (hb : 0 < b)
    (A : OraclePolicy.AdaptivePolicy (dualDomain K b hb) (n := p.n) (dx := dx) Ω)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ) (seed : Ω) :
    OracleProgram.eval (simulationProgram (a := a) A y0 hy0 x0 T) (oracleResponse P) seed =
      b • (OraclePolicy.run (dualDomain K b hb) A (oracleResponse (toProblem P ha hb)) seed T).1 := by
  rw [simulationProgram, OracleProgram.eval_map, OracleSimulation.eval_program]
  have he : (fun q ↦ targetReply (a := a) q (oracleResponse P (sourceQuery q))) =
      oracleResponse (toProblem P ha hb) := funext (fun q ↦ (exact_reply P ha hb q).symm)
  rw [he]

def simulationPolicy
    (A : RandomizedPolicy (dualDomain K b hb) (n := p.n) (dx := dx))
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ) :
    RandomizedPolicy K (n := p.n) (dx := dx) := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  exact OracleProgram.randomizedPolicy K (simulationProgram (a := a) A.policy y0 hy0 x0 T) A.law

theorem success_simulation (P : Problem p dx dy K) (hP : P.individualSmooth)
    (ha : 0 < a) (hb : 0 < b)
    (A : RandomizedPolicy (dualDomain K b hb) (n := p.n) (dx := dx))
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ)
    (hA : Success A (toProblem P ha hb) T) :
    Success (simulationPolicy (a := a) A y0 hy0 x0 T) P T := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  change Success (OracleProgram.randomizedPolicy K
    (simulationProgram (a := a) A.policy y0 hy0 x0 T) A.law) P T
  rw [OracleProgram.success_iff]
  simp_rw [eval_simulationProgram P ha hb]
  have hAS := P.individual_implies_averaged hP
  have hSAS := (toProblem P ha hb).individual_implies_averaged (toProblem_individualSmooth P ha hb hP)
  have hout := (continuous_const_smul b).measurable.comp
    (randomizedOutput_measurable A (toProblem P ha hb) hSAS T)
  have hm := P.moreau_gradient_continuous hAS |>.measurable.comp hout
  have hset : {seed | StationaryOutput P (b • randomizedOutput A (toProblem P ha hb) T seed)} =
      {seed | ‖gradient (problemMoreauEnvelope P) (b • randomizedOutput A (toProblem P ha hb) T seed)‖ ≤
        p.epsilon} := by
    ext seed
    exact P.stationaryOutput_iff hAS _
  refine ⟨?_, hA.2.trans (measure_mono ?_)⟩
  · change MeasurableSet {seed | StationaryOutput P (b • randomizedOutput A (toProblem P ha hb) T seed)}
    rw [hset]
    exact measurableSet_le hm.norm measurable_const
  · intro seed hseed
    exact stationary_transfer P hP ha hb _ hseed

theorem validBudget_source_of_scaled (p : ProblemParameters) (ha : 0 < a) (hb : 0 < b)
    {T : ℕ} (hT : ValidBudget (parameters p a b ha hb) .individual T) :
    ValidBudget p .individual T := by
  intro dx dy K x0
  obtain ⟨A, hA⟩ := hT dx dy (dualDomain K b hb) (b⁻¹ • x0)
  obtain ⟨y0, hy0⟩ := K.nonempty
  refine ⟨simulationPolicy (p := p) (a := a) A y0 hy0 x0 T, ?_⟩
  intro P h0 hP
  apply success_simulation P hP ha hb A y0 hy0 x0 T
  apply hA (toProblem P ha hb)
  · change b⁻¹ • P.initialPoint = b⁻¹ • x0
    rw [h0]
  · exact toProblem_individualSmooth P ha hb hP

theorem lowerBudget_transfer (p : ProblemParameters) (ha : 0 < a) (hb : 0 < b)
    {bound : ℝ} (h : LowerBudgetBound p .individual bound) :
    LowerBudgetBound (parameters p a b ha hb) .individual bound := by
  intro T hT
  exact h T (validBudget_source_of_scaled p ha hb hT)

end NCConcave16991.ProblemScaling
