import NCConcave16991.ReplicationProblem
import NCConcave16991.OracleSimulation
import NCConcave16991.OracleProgramProbability
import NCConcave16991.UpperAssembly

/-! # Complete balanced replication in the unrestricted randomized oracle model -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991.Replication

variable {p : ProblemParameters} {s dx dy : ℕ} {hs : 0 < s}
  {K : KnownDualDomain dy p.diameter}

def sourceQuery (q : OracleQuery p.n dx K) : OracleQuery s dx K :=
  (sourceIndex s hs q.1, q.2)

def targetReply (q : OracleQuery p.n dx K) (r : OracleAnswer dx dy) : OracleAnswer dx dy :=
  weight p.n s (q.1.val % s) • r

theorem sourceQuery_measurable : Measurable (sourceQuery (hs := hs) (p := p) (dx := dx) (K := K)) :=
  ((measurable_of_countable (sourceIndex s hs)).comp measurable_fst).prodMk measurable_snd

theorem targetReply_measurable : Measurable
    (Function.uncurry (targetReply (p := p) (s := s) (dx := dx) (K := K))) :=
  ((measurable_of_countable (fun i : Fin p.n ↦ weight p.n s (i.val % s))).comp
    (measurable_fst.comp measurable_fst)).smul measurable_snd

theorem exact_reply (P : Problem (sourceParameters p s hs) dx dy K) (hsn : s ≤ p.n)
    (q : OracleQuery p.n dx K) :
    oracleResponse (toProblem P hsn) q = targetReply (s := s) q (oracleResponse P (sourceQuery (hs := hs) q)) := by
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]

def simulationProgram (A : OraclePolicy.AdaptivePolicy K (n := p.n) (dx := dx) Ω)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ) :
    OracleProgram.ProblemProgram K (n := s) (dx := dx) Ω T :=
  OracleSimulation.program K A (⟨0, hs⟩, x0, ⟨y0, hy0⟩)
    (sourceQuery (hs := hs)) (targetReply (s := s)) sourceQuery_measurable (targetReply_measurable (s := s)) T

theorem eval_simulationProgram (P : Problem (sourceParameters p s hs) dx dy K)
    (hsn : s ≤ p.n) (A : OraclePolicy.AdaptivePolicy K (n := p.n) (dx := dx) Ω)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ) (seed : Ω) :
    OracleProgram.eval (simulationProgram (hs := hs) A y0 hy0 x0 T) (oracleResponse P) seed =
      (OraclePolicy.run K A (oracleResponse (toProblem P hsn)) seed T).1 := by
  rw [simulationProgram, OracleSimulation.eval_program]
  have he : (fun q ↦ targetReply (s := s) q (oracleResponse P (sourceQuery (hs := hs) q))) =
      oracleResponse (toProblem P hsn) := funext (fun q ↦ (exact_reply P hsn q).symm)
  rw [he]

def simulationPolicy (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ) :
    RandomizedPolicy K (n := s) (dx := dx) := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  exact OracleProgram.randomizedPolicy (n := s) K (simulationProgram (p := p) (hs := hs) A.policy y0 hy0 x0 T) A.law

theorem success_simulation (P : Problem (sourceParameters p s hs) dx dy K)
    (hsn : s ≤ p.n) (hP : P.individualSmooth)
    (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (T : ℕ)
    (hA : Success A (toProblem P hsn) T) :
    Success (simulationPolicy (p := p) (hs := hs) A y0 hy0 x0 T) P T := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  change Success (p := sourceParameters p s hs) (OracleProgram.randomizedPolicy (n := s) K
    (simulationProgram (p := p) (hs := hs) A.policy y0 hy0 x0 T) A.law) P T
  rw [OracleProgram.success_iff (p := sourceParameters p s hs)]
  simp_rw [eval_simulationProgram P hsn]
  have hAS := P.individual_implies_averaged hP
  have hTAS := (toProblem P hsn).individual_implies_averaged (toProblem_individualSmooth P hsn hP)
  have hm := (P.moreau_gradient_continuous hAS).measurable.comp
    (randomizedOutput_measurable A (toProblem P hsn) hTAS T)
  have hset : {seed | StationaryOutput P (randomizedOutput A (toProblem P hsn) T seed)} =
      {seed | ‖gradient (problemMoreauEnvelope P) (randomizedOutput A (toProblem P hsn) T seed)‖ ≤
        (sourceParameters p s hs).epsilon} := by
    ext seed
    exact P.stationaryOutput_iff hAS _
  refine ⟨?_, hA.2.trans (measure_mono ?_)⟩
  · change MeasurableSet {seed | StationaryOutput P (randomizedOutput A (toProblem P hsn) T seed)}
    rw [hset]
    exact measurableSet_le hm.norm measurable_const
  · intro seed hseed
    exact stationary_transfer P hsn hP _ hseed

/-- The chosen source policy uses only public parameters and the target policy,
and is selected before the unknown source Problem. Every seed and fixed budget
is preserved, including paths on which the target policy stops early. -/
theorem validBudget_source_of_target (p : ProblemParameters) (s : ℕ)
    (hs : 0 < s) (hsn : s ≤ p.n) {T : ℕ} (hT : ValidBudget p .individual T) :
    ValidBudget (sourceParameters p s hs) .individual T := by
  intro dx dy K x0
  obtain ⟨A, hA⟩ := hT dx dy K x0
  obtain ⟨y0, hy0⟩ := K.nonempty
  refine ⟨simulationPolicy (p := p) (hs := hs) A y0 hy0 x0 T, ?_⟩
  intro P h0 hP
  exact success_simulation P hsn hP A y0 hy0 x0 T
    (hA (toProblem P hsn) h0 (toProblem_individualSmooth P hsn hP))

theorem lowerBudget_transfer (p : ProblemParameters) (s : ℕ) (hs : 0 < s)
    (hsn : s ≤ p.n) {b : ℝ}
    (h : LowerBudgetBound (sourceParameters p s hs) .individual b) :
    LowerBudgetBound p .individual b := by
  intro T hT
  exact h T (validBudget_source_of_target p s hs hsn hT)

end NCConcave16991.Replication
