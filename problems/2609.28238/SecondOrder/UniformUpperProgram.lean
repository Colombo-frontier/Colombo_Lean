import SecondOrder.BudgetRunProgram
import SecondOrder.StochasticUpperAlgorithm

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def postChordSeedLaw (L : ℕ) (δ : ℝ) : Measure (PostChordSeed L δ) :=
  Measure.infinitePi (fun _ : BinaryNode L => batchTapeLaw unitLine (confidenceRepeats δ))

instance postChordSeedLaw_probability (L : ℕ) (δ : ℝ) : IsProbabilityMeasure (postChordSeedLaw L δ) := by
  unfold postChordSeedLaw
  infer_instance

def trackingProgramSeedLaw (P : Parameters) (d L : ℕ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    Measure (TrackingProgramSeed d L P γ δ) :=
  (branchedOjaSeedLaw P d hγ δ).prod
    ((PMF.uniformOfFintype Bool).toMeasure.prod (postChordSeedLaw L δ))

instance trackingProgramSeedLaw_probability (P : Parameters) (d L : ℕ) {γ : ℝ}
    (hγ : 0<γ) (δ : ℝ) : IsProbabilityMeasure (trackingProgramSeedLaw P d L hγ δ) := by
  unfold trackingProgramSeedLaw
  infer_instance

abbrev UniformUpperSeed (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) :=
  let M := physicalCap P ν (ε/10) γ
  Fin M → TrackingProgramSeed d (trackingTreeDepth M) P γ (localFailureTolerance M)

/-- The entire algorithm's private law is fixed before the unknown sample
space, sample law and common loss are chosen. -/
def uniformUpperSeedLaw (P : Parameters) (ν : ℝ) (d : ℕ) (ε : ℝ) {γ : ℝ} (hγ : 0<γ) :
    Measure (UniformUpperSeed P ν d ε γ) :=
  let M := physicalCap P ν (ε/10) γ
  Measure.pi (fun _ : Fin M => trackingProgramSeedLaw P d (trackingTreeDepth M) hγ (localFailureTolerance M))

instance uniformUpperSeedLaw_probability (P : Parameters) (ν : ℝ) (d : ℕ) (ε : ℝ)
    {γ : ℝ} (hγ : 0<γ) : IsProbabilityMeasure (uniformUpperSeedLaw P ν d ε hγ) := by
  unfold uniformUpperSeedLaw
  infer_instance

def uniformUpperProgram (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ)
    (seeds : UniformUpperSeed P ν d ε γ) : OracleProgram (HvpQuery d) (Point d) (Point d) :=
  let M := physicalCap P ν (ε/10) γ
  budgetRunPointProgram P (trackingEpochLength P (ε/10)) (stochasticUpperCap P ν d ε γ)
    P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10) (trackingChordTolerance (ε/10) M)
    γ (localFailureTolerance M) M seeds

theorem uniformUpperProgram_measurable (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (uniformUpperProgram P ν d ε γ) := by
  have hh := budgetRunPointProgram_measurable (d := d)
    (L := trackingTreeDepth (physicalCap P ν (ε/10) γ))
    P (trackingEpochLength P (ε/10)) (stochasticUpperCap P ν d ε γ)
    P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10)
    (trackingChordTolerance (ε/10) (physicalCap P ν (ε/10) γ))
    γ (localFailureTolerance (physicalCap P ν (ε/10) γ)) (physicalCap P ν (ε/10) γ)
  exact hh

theorem uniformUpperProgram_usesAtMost (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ)
    (seeds : UniformUpperSeed P ν d ε γ) :
    OracleProgram.UsesAtMost (stochasticUpperCap P ν d ε γ) (uniformUpperProgram P ν d ε γ seeds) := by
  have hh := budgetRunPointProgram_usesAtMost P (trackingEpochLength P (ε/10))
    (stochasticUpperCap P ν d ε γ) P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10)
    (trackingChordTolerance (ε/10) (physicalCap P ν (ε/10) γ))
    γ (localFailureTolerance (physicalCap P ν (ε/10) γ)) (physicalCap P ν (ε/10) γ) seeds
  exact hh

def uniformUpperAlgorithm (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ)
    (seeds : UniformUpperSeed P ν d ε γ) : HvpAlgorithm d (ℕ → Point d) :=
  OracleProgram.algorithm (.grad 0) 0 0 (uniformUpperProgram P ν d ε γ seeds)

theorem uniformUpperAlgorithm_measurable (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) :
    MeasurableOracleAlgorithmFamily (uniformUpperAlgorithm P ν d ε γ) :=
  OracleProgram.algorithm_measurable 0 (uniformUpperProgram_measurable P ν d ε γ)

/-- All branches finish within the manuscript's original hard cap. The
claim holds for arbitrary reply functions, without accuracy assumptions. -/
theorem uniformUpperProgram_finishes {Ω : Type} (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ)
    (seeds : UniformUpperSeed P ν d ε γ) (reply : HvpQuery d → Ω → Point d) (zs : ℕ → Ω) :
    ∃ x, OracleProgram.run (.grad 0) reply zs (uniformUpperProgram P ν d ε γ seeds)
      (stochasticUpperCap P ν d ε γ)=.done x :=
  OracleProgram.run_done (.grad 0) reply zs (uniformUpperProgram_usesAtMost P ν d ε γ seeds)

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The success probability required by the minimax definition is the
actual compiled program's output law. The full sampler correspondence is
proved downstream in `UniformUpperOutputLaw`. -/
theorem CommonLoss.uniformUpperAlgorithm_probability (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (ε : ℝ) {γ : ℝ} (hγ : 0<γ) :
    hvpAlgorithmSospProbability (uniformUpperSeedLaw P ν d ε hγ) μ
      (uniformUpperAlgorithm P ν d ε γ) F f ε γ (stochasticUpperCap P ν d ε γ)=
      (OracleProgram.seededOutputLaw μ (uniformUpperSeedLaw P ν d ε hγ) (.grad 0) 0
        (fun q z => hvpReply f z q) (uniformUpperProgram P ν d ε γ) (stochasticUpperCap P ν d ε γ)).real
        {x | IsSOSP F ε γ x} := by
  have he := OracleProgram.algorithm_seeded_history_event μ (uniformUpperSeedLaw P ν d ε hγ)
    (.grad 0) 0 0 a₀ (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
    (uniformUpperProgram P ν d ε γ) (uniformUpperProgram_measurable P ν d ε γ)
    (stochasticUpperCap P ν d ε γ) {x | IsSOSP F ε γ x} (isSOSP_measurableSet h.population_smooth ε γ)
  exact congrArg ENNReal.toReal he

end
end SecondOrder
