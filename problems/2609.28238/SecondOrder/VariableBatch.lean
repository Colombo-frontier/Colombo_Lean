import SecondOrder.BatchTape

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

variable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def variableFreshEstimate (X : A × Ω → E) (V : A → ℝ) (ρ δ : ℝ)
    (w : A × BatchTape Ω (confidenceRepeats δ)) : E :=
  robustBatch (fun z => X (w.1,z)) (localBatchSize (V w.1) ρ)
    (confidenceRepeats_pos δ) ρ (w.2 (localBatchSize (V w.1) ρ))

theorem variableFreshEstimate_eq (X : A × Ω → E) (V : A → ℝ) (ρ δ : ℝ)
    (a : A) (w : BatchTape Ω (confidenceRepeats δ)) :
    variableFreshEstimate X V ρ δ (a,w) =
      freshEstimate (fun z => X (a,z)) (V a) ρ δ (w (localBatchSize (V a) ρ)) := rfl

theorem variableFreshEstimate_measurable {X : A × Ω → E} {V : A → ℝ}
    (hX : Measurable X) (hV : Measurable V) (ρ δ : ℝ) :
    Measurable (variableFreshEstimate X V ρ δ) := by
  let eval : (A × BatchTape Ω (confidenceRepeats δ)) × ℕ → E := fun w =>
    robustBatch (fun z => X (w.1.1,z)) w.2 (confidenceRepeats_pos δ) ρ (w.1.2 w.2)
  have he : Measurable eval := by
    apply measurable_from_prod_countable
    intro m
    apply Measurable.comp (f := fun w : A × BatchTape Ω (confidenceRepeats δ) => (w.1,w.2 m))
      (robustBatch_joint_measurable (X := X) hX m (confidenceRepeats_pos δ) ρ)
    exact measurable_fst.prodMk ((measurable_pi_apply m).comp measurable_snd)
  exact he.comp (f := fun w : A × BatchTape Ω (confidenceRepeats δ) =>
    (w,localBatchSize (V w.1) ρ))
    (measurable_id.prodMk ((localBatchSize_measurable hV ρ).comp measurable_fst))

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure A} [IsProbabilityMeasure η]

/-- The selected batch has the fixed-endpoint law exactly. There is no
replacement by a larger, uniform batch and no conditional-independence axiom. -/
theorem variableFreshEstimate_slice_confidence {X : A × Ω → E} {V : A → ℝ} {target : A → E}
    (hX : Measurable X) (ρ δ : ℝ)
    (hconf : ∀ a, localLaw μ (V a) ρ δ
      {z | ρ < ‖freshEstimate (fun ω => X (a,ω)) (V a) ρ δ z-target a‖} ≤ ENNReal.ofReal δ)
    (a : A) :
    batchTapeLaw μ (confidenceRepeats δ)
      {w | ρ < ‖variableFreshEstimate X V ρ δ (a,w)-target a‖} ≤ ENNReal.ofReal δ := by
  have hm : Measurable (freshEstimate (fun ω => X (a,ω)) (V a) ρ δ) :=
    robustBatch_measurable (hX.comp (measurable_const.prodMk measurable_id))
      _ (confidenceRepeats_pos δ) ρ
  have he := batchTapeLaw_eval μ (confidenceRepeats δ) (localBatchSize (V a) ρ)
    (measurableSet_lt (measurable_const (a := ρ)) (hm.sub_const (target a)).norm)
  change batchTapeLaw μ (confidenceRepeats δ)
    ((fun w => w (localBatchSize (V a) ρ)) ⁻¹'
      {z | ρ < ‖freshEstimate (fun ω => X (a,ω)) (V a) ρ δ z-target a‖}) ≤ ENNReal.ofReal δ
  rw [he]
  exact hconf a

theorem variableFreshEstimate_past_confidence {X : A × Ω → E} {V : A → ℝ} {target : A → E}
    (hX : Measurable X) (hV : Measurable V) (ht : Measurable target) (ρ δ : ℝ)
    (hconf : ∀ a, localLaw μ (V a) ρ δ
      {z | ρ < ‖freshEstimate (fun ω => X (a,ω)) (V a) ρ δ z-target a‖} ≤ ENNReal.ofReal δ)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (batchTapeLaw μ (confidenceRepeats δ)))
      {w | w.1 ∈ past ∧ ρ < ‖variableFreshEstimate X V ρ δ w-target w.1‖} ≤
        ENNReal.ofReal δ*η past :=
  fresh_event_past_bound
    (measurableSet_lt measurable_const ((variableFreshEstimate_measurable hX hV ρ δ).sub
      (ht.comp measurable_fst)).norm)
    (variableFreshEstimate_slice_confidence hX ρ δ hconf) hp

theorem variableFreshEstimate_confidence {X : A × Ω → E} {V : A → ℝ} {target : A → E}
    (hX : Measurable X) (hV : Measurable V) (ht : Measurable target) (ρ δ : ℝ)
    (hconf : ∀ a, localLaw μ (V a) ρ δ
      {z | ρ < ‖freshEstimate (fun ω => X (a,ω)) (V a) ρ δ z-target a‖} ≤ ENNReal.ofReal δ) :
    (η.prod (batchTapeLaw μ (confidenceRepeats δ)))
      {w | ρ < ‖variableFreshEstimate X V ρ δ w-target w.1‖} ≤ ENNReal.ofReal δ := by
  simpa using variableFreshEstimate_past_confidence (η := η) hX hV ht ρ δ hconf MeasurableSet.univ

end
end SecondOrder
