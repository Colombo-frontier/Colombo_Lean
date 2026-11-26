import SecondOrder.OriginalBudgetRunLaw

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The uniform reply-only algorithm has exactly the original sampler's
output law, including every adaptive branch and the deterministic cap. -/
theorem CommonLoss.uniformUpperProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (ε : ℝ) {γ : ℝ} (hγ : 0<γ) :
    OracleProgram.seededOutputLaw μ (uniformUpperSeedLaw P ν d ε hγ) (.grad 0) 0
      (fun q a => hvpReply f a q) (uniformUpperProgram P ν d ε γ) (stochasticUpperCap P ν d ε γ)=
      Measure.map (fun w : (StochasticUpperTape Ω d P ν ε γ : Type) =>
        (stochasticUpperRun P ν f ε γ w).1.physical.point)
        (stochasticUpperLaw μ P ν d ε hγ) := by
  have hp := budgetRunPointProgram_outputLaw μ P (trackingEpochLength P (ε/10))
    (stochasticUpperCap P ν d ε γ) P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10)
    (trackingChordTolerance (ε/10) (physicalCap P ν (ε/10) γ)) γ
    (localFailureTolerance (physicalCap P ν (ε/10) γ))
    (trackingProgramSeedLaw P d (trackingTreeDepth (physicalCap P ν (ε/10) γ)) hγ
      (localFailureTolerance (physicalCap P ν (ε/10) γ)))
    a₀ (fun q a => hvpReply f a q) h.hvpReply_joint_measurable (physicalCap P ν (ε/10) γ)
  have hb := h.budgetRunProgram_original_outputLaw (L := trackingTreeDepth (physicalCap P ν (ε/10) γ))
    a₀ (trackingEpochLength P (ε/10)) (stochasticUpperCap P ν d ε γ)
    P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10)
    (trackingChordTolerance (ε/10) (physicalCap P ν (ε/10) γ)) hγ
    (localFailureTolerance (physicalCap P ν (ε/10) γ)) (physicalCap P ν (ε/10) γ)
  rw [hb] at hp
  change _=Measure.map (fun z => z.1.physical.point)
    (Measure.map (stochasticUpperRun P ν f ε γ) (stochasticUpperLaw μ P ν d ε hγ)) at hp
  rw [Measure.map_map
    (state_measurable_fields.mp ((tracked_measurable_fields.mp measurable_fst).1)).1
    (h.stochasticUpperRun_measurable ε γ)] at hp
  exact hp

theorem CommonLoss.uniformUpperProgram_success (h : CommonLoss μ P ν F f)
    (a₀ : Ω) {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    ENNReal.ofReal (29/32:ℝ) ≤
      OracleProgram.seededOutputLaw μ (uniformUpperSeedLaw P ν d ε hγ) (.grad 0) 0
        (fun q a => hvpReply f a q) (uniformUpperProgram P ν d ε γ) (stochasticUpperCap P ν d ε γ)
        {x | IsSOSP F ε γ x} := by
  rw [h.uniformUpperProgram_outputLaw a₀ ε hγ]
  have hm : Measurable (fun w : (StochasticUpperTape Ω d P ν ε γ : Type) =>
      (stochasticUpperRun P ν f ε γ w).1.physical.point) :=
    (state_measurable_fields.mp ((tracked_measurable_fields.mp
      (h.stochasticUpperRun_measurable ε γ).fst).1)).1
  rw [Measure.map_apply hm (isSOSP_measurableSet h.population_smooth ε γ)]
  apply (h.stochasticUpperRun_success hε hγ).trans
  apply measure_mono
  intro w hw
  exact hw.2.2

theorem CommonLoss.uniformUpperProgram_probability (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (ε : ℝ) {γ : ℝ} (hγ : 0<γ) :
    IsProbabilityMeasure (OracleProgram.seededOutputLaw μ (uniformUpperSeedLaw P ν d ε hγ)
      (.grad 0) 0 (fun q a => hvpReply f a q) (uniformUpperProgram P ν d ε γ)
      (stochasticUpperCap P ν d ε γ)) := by
  rw [h.uniformUpperProgram_outputLaw a₀ ε hγ]
  exact isProbabilityMeasure_map
    (state_measurable_fields.mp ((tracked_measurable_fields.mp
      (h.stochasticUpperRun_measurable ε γ).fst).1)).1.aemeasurable

theorem CommonLoss.uniformUpperAlgorithm_success (h : CommonLoss μ P ν F f)
    (a₀ : Ω) {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    29/32 ≤ hvpAlgorithmSospProbability (uniformUpperSeedLaw P ν d ε hγ) μ
      (uniformUpperAlgorithm P ν d ε γ) F f ε γ (stochasticUpperCap P ν d ε γ) := by
  rw [h.uniformUpperAlgorithm_probability a₀ ε hγ]
  letI := h.uniformUpperProgram_probability a₀ ε hγ
  have hh := ENNReal.toReal_mono (measure_ne_top _ _)
    (h.uniformUpperProgram_success a₀ hε hγ)
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤29/32)] using hh

end
end SecondOrder
