import SecondOrder.RobustBatch
import SecondOrder.ContinuousChord

open MeasureTheory

namespace SecondOrder
noncomputable section

abbrev LocalDraws (Ω : Type*) (V ρ δ : ℝ) :=
  Draws (Draws Ω (localBatchSize V ρ)) (confidenceRepeats δ)

def localLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (V ρ δ : ℝ) :
    Measure (LocalDraws Ω V ρ δ) :=
  drawsLaw (drawsLaw μ (localBatchSize V ρ)) (confidenceRepeats δ)

instance localLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (V ρ δ : ℝ) : IsProbabilityMeasure (localLaw μ V ρ δ) :=
  inferInstanceAs (IsProbabilityMeasure (drawsLaw (drawsLaw μ (localBatchSize V ρ)) (confidenceRepeats δ)))

def localQueryCount (V ρ δ : ℝ) : ℕ := localBatchSize V ρ*confidenceRepeats δ

def freshEstimate {Ω E : Type*} [AddZeroClass E] [SMul ℝ E] [PseudoMetricSpace E]
    (X : Ω → E) (V ρ δ : ℝ) (w : LocalDraws Ω V ρ δ) : E :=
  robustCenter (confidenceRepeats_pos δ)
    (drawsVector (drawsMean X (localBatchSize V ρ)) (confidenceRepeats δ) w) (ρ/3)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

def gradientAnchor (P : Parameters) (f : Ω → Point d → ℝ) (x : Point d) (ρ δ : ℝ) :
    LocalDraws Ω (P.gradientNoise^2) ρ δ → Point d :=
  freshEstimate (fun z => gradient (f z) x) (P.gradientNoise^2) ρ δ

def chordVariance (P : Parameters) (x y : Point d) : ℝ :=
  (P.hessianNoise^2+P.gradientLip^2)*‖y-x‖^2

def freshChord (P : Parameters) (f : Ω → Point d → ℝ) (x y : Point d) (ρ δ : ℝ) :
    LocalDraws (ℝ × Ω) (chordVariance P x y) ρ δ → Point d :=
  freshEstimate (randomLineHvp f x y) (chordVariance P x y) ρ δ

theorem CommonLoss.anchor_measurable (h : CommonLoss μ P ν F f) (x : Point d) (ρ δ : ℝ) :
    Measurable (gradientAnchor P f x ρ δ) :=
  robustBatch_measurable
    (h.gradient_measurable.comp (measurable_id.prodMk measurable_const))
    _ (confidenceRepeats_pos δ) ρ

/-- The fresh-gradient anchor with explicit sampling law and accuracy. -/
theorem CommonLoss.anchor_confidence (h : CommonLoss μ P ν F f) (x : Point d)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    localLaw μ (P.gradientNoise^2) ρ δ
      {w | ρ < ‖gradientAnchor P f x ρ δ w-gradient F x‖} ≤ ENNReal.ofReal δ :=
  robustBatch_confidence
    (h.gradient_measurable.comp (measurable_id.prodMk measurable_const))
    (h.gradient_integrable x) (h.gradient_error_integrable x) (h.gradient_unbiased x)
    (h.gradient_variance x) hρ hδ

theorem anchor_query_count (P : Parameters) {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (localQueryCount (P.gradientNoise^2) ρ δ : ℝ) ≤
      (36*P.gradientNoise^2/ρ^2+2)*(8*Real.log (1/δ)+2) :=
  robustBatch_query_count (sq_nonneg _) hδ hδ1

theorem CommonLoss.chord_measurable (h : CommonLoss μ P ν F f) (x y : Point d) (ρ δ : ℝ) :
    Measurable (freshChord P f x y ρ δ) :=
  robustBatch_measurable (h.randomLine_measurable x y) _ (confidenceRepeats_pos δ) ρ

/-- The random-line HVP chord estimate for deterministic endpoints, with
continuous line positions, arbitrary sample laws and explicit confidence. -/
theorem CommonLoss.chord_confidence (h : CommonLoss μ P ν F f) (x y : Point d)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    localLaw (unitLine.prod μ) (chordVariance P x y) ρ δ
      {w | ρ < ‖freshChord P f x y ρ δ w-(gradient F y-gradient F x)‖} ≤ ENNReal.ofReal δ :=
  robustBatch_confidence (h.randomLine_measurable x y) (h.randomLine_integrable x y)
    (integrable_norm_sub_sq (h.randomLine_integrable x y) (h.randomLine_sq_integrable x y) _)
    (h.randomLine_unbiased x y) (h.randomLine_variance x y) hρ hδ

theorem chord_query_count (P : Parameters) (x y : Point d) {ρ δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (localQueryCount (chordVariance P x y) ρ δ : ℝ) ≤
      (36*(P.hessianNoise^2+P.gradientLip^2)*‖y-x‖^2/ρ^2+2)*(8*Real.log (1/δ)+2) := by
  have h := robustBatch_query_count (ρ := ρ) (show 0 ≤ chordVariance P x y by
    dsimp [chordVariance]; positivity) hδ hδ1
  simpa only [localQueryCount, chordVariance, mul_assoc] using h

/-- Every individual chord observation is exactly one permitted fresh HVP
reply at a single query point. -/
theorem randomLine_one_query (f : Ω → Point d → ℝ) (x y : Point d) (t : ℝ) (z : Ω) :
    randomLineHvp f x y (t,z) = hvpReply f z (.hvp (x+t•(y-x)) (y-x)) := rfl

end
end SecondOrder
