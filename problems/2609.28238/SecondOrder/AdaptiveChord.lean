import SecondOrder.VariableBatch

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure A} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

def adaptiveChord (P : Parameters) (f : Ω → Point d → ℝ) (x y : A → Point d) (ρ δ : ℝ) :
    A × BatchTape (ℝ × Ω) (confidenceRepeats δ) → Point d :=
  variableFreshEstimate (fun w => randomLineHvp f (x w.1) (y w.1) w.2)
    (fun a => chordVariance P (x a) (y a)) ρ δ

theorem chordVariance_measurable (P : Parameters) {x y : A → Point d}
    (hx : Measurable x) (hy : Measurable y) : Measurable (fun a => chordVariance P (x a) (y a)) :=
  ((hy.sub hx).norm.pow_const 2).const_mul _

theorem CommonLoss.randomLine_adaptive_measurable (h : CommonLoss μ P ν F f)
    {x y : A → Point d} (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun w : A × (ℝ × Ω) => randomLineHvp f (x w.1) (y w.1) w.2) := by
  have hdir : Measurable (fun w : A × (ℝ × Ω) => y w.1-x w.1) :=
    (hy.sub hx).comp measurable_fst
  have hpt : Measurable (fun w : A × (ℝ × Ω) => x w.1+w.2.1•(y w.1-x w.1)) :=
    (hx.comp measurable_fst).add (measurable_snd.fst.smul hdir)
  have hH := h.hessian_measurable.comp (measurable_snd.snd.prodMk hpt)
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp (hH.prodMk hdir)

theorem CommonLoss.adaptiveChord_measurable (h : CommonLoss μ P ν F f)
    {x y : A → Point d} (hx : Measurable x) (hy : Measurable y) (ρ δ : ℝ) :
    Measurable (adaptiveChord P f x y ρ δ) :=
  variableFreshEstimate_measurable (h.randomLine_adaptive_measurable hx hy)
    (chordVariance_measurable P hx hy) ρ δ

/-- Both endpoints can depend on the entire past. The batch length is the
manuscript's actual chord-dependent ceil, chosen before reading new samples. -/
theorem CommonLoss.adaptiveChord_past_confidence (h : CommonLoss μ P ν F f)
    {x y : A → Point d} (hx : Measurable x) (hy : Measurable y)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) {past : Set A} (hp : MeasurableSet past) :
    (η.prod (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)))
      {w | w.1 ∈ past ∧ ρ < ‖adaptiveChord P f x y ρ δ w-(gradient F (y w.1)-gradient F (x w.1))‖} ≤
        ENNReal.ofReal δ*η past := by
  have hg := (contDiff_gradient_one h.population_smooth).continuous.measurable
  exact variableFreshEstimate_past_confidence (h.randomLine_adaptive_measurable hx hy)
    (chordVariance_measurable P hx hy) ((hg.comp hy).sub (hg.comp hx)) ρ δ
    (fun a => h.chord_confidence (x a) (y a) hρ hδ) hp

theorem CommonLoss.adaptiveChord_confidence (h : CommonLoss μ P ν F f)
    {x y : A → Point d} (hx : Measurable x) (hy : Measurable y)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    (η.prod (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)))
      {w | ρ < ‖adaptiveChord P f x y ρ δ w-(gradient F (y w.1)-gradient F (x w.1))‖} ≤ ENNReal.ofReal δ := by
  simpa using h.adaptiveChord_past_confidence (η := η) hx hy hρ hδ MeasurableSet.univ

def adaptiveChordCost (P : Parameters) (x y : A → Point d) (ρ δ : ℝ) (a : A) : ℕ :=
  localQueryCount (chordVariance P (x a) (y a)) ρ δ

theorem adaptiveChordCost_measurable (P : Parameters) {x y : A → Point d}
    (hx : Measurable x) (hy : Measurable y) (ρ δ : ℝ) :
    Measurable (adaptiveChordCost P x y ρ δ) :=
  (localBatchSize_measurable (chordVariance_measurable P hx hy) ρ).mul_const (confidenceRepeats δ)

theorem adaptiveChordCost_bound (P : Parameters) (x y : A → Point d) {ρ δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a : A) :
    (adaptiveChordCost P x y ρ δ a : ℝ) ≤
      (36*(P.hessianNoise^2+P.gradientLip^2)*‖y a-x a‖^2/ρ^2+2)*(8*Real.log (1/δ)+2) :=
  chord_query_count P (x a) (y a) hδ hδ1

end
end SecondOrder
