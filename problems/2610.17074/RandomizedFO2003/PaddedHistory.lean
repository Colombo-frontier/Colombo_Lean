import RandomizedFO2003.PaddedExposure

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

/-- Each exposure first draws an auxiliary ambient vector and then reveals
a direction in the current residual coordinate space. -/
def PaddedHistory (E : Type) (d : ℕ) : (n : ℕ) → Type u → Type u
  | 0, Ω => Ω
  | n + 1, Ω => PaddedHistory E d n ((Ω × E) × Coordinates (d + n + 1))

instance paddedHistoryMeasurableSpace (E : Type) [MeasurableSpace E] (d : ℕ) :
    (n : ℕ) → (Ω : Type u) → [MeasurableSpace Ω] → MeasurableSpace (PaddedHistory E d n Ω)
  | 0, _, m => m
  | n + 1, Ω, _ => paddedHistoryMeasurableSpace E d n ((Ω × E) × Coordinates (d + n + 1))

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def paddedHistoryLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (d : ℕ) :
    (n : ℕ) → {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω → Measure (PaddedHistory E d n Ω)
  | 0, _, _, μ => μ
  | n + 1, _, _, μ => paddedHistoryLaw E d n
      ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw (Coordinates (d + n + 1))))

instance paddedHistoryLaw_sFinite (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] : SFinite (paddedHistoryLaw E d n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (SFinite μ)
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite ((μ.prod (Spherical.sphereLaw E)).prod
        (Spherical.sphereLaw (Coordinates (d + n + 1)))) := Measure.prod.instSFinite
    exact ih _

instance paddedHistoryLaw_probability (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (paddedHistoryLaw E d n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => exact ih _

noncomputable def paddedFrameNext {m : ℕ} {Ω : Type u} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (x : Ω → E)
    (p : (Ω × E) × Coordinates (m + 1)) : ExposureFrame (Coordinates m) E :=
  (F p.1.1).paddedNext kind (x p.1.1) p.1.2 p.2

theorem measurable_paddedFrameNext {m : ℕ} {Ω : Type u} [MeasurableSpace Ω] (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (hF : ExposureFrame.MeasurableFamily F)
    (x : Ω → E) (hx : Measurable x) : ExposureFrame.MeasurableFamily (paddedFrameNext kind F x) :=
  ExposureFrame.MeasurableFamily.paddedNext (n := m) (F := fun p : Ω × E => F p.1)
    (x := fun p => x p.1) (auxiliary := Prod.snd) (hF.comp measurable_fst) kind
      (hx.comp measurable_fst) measurable_snd

noncomputable def paddedObservedHistory {m : ℕ} {H Ω : Type u}
    [MeasurableSpace H] (request : ExposureRequest H E)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (history : Ω → H)
    (p : (Ω × E) × Coordinates (m + 1)) : H × E :=
  (history p.1.1, (F p.1.1).exposedValue request.kind (request.vector (history p.1.1)) p.2)

theorem measurable_paddedObservedHistory {m : ℕ} {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (request : ExposureRequest H E)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) :
    Measurable (paddedObservedHistory request F history) :=
  measurable_observedHistory request (fun p : Ω × E => F p.1) (hF.comp measurable_fst)
    (fun p => history p.1) (hh.comp measurable_fst)

noncomputable def ActionProgram.paddedHistoryMap (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) →
      PaddedHistory E d n Ω → ActionHistory E n H
  | 0, _, _, _, _, _, _, history => history
  | n + 1, _, _, _, _, plan, F, history =>
    paddedHistoryMap d n plan.2 (paddedFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (paddedObservedHistory plan.1 F history)

theorem ActionProgram.paddedHistoryMap_measurable (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) : Measurable (plan.paddedHistoryMap d n F history) := by
  induction n generalizing H Ω with
  | zero => exact hh
  | succ n ih =>
    exact ih plan.2 _ (measurable_paddedFrameNext plan.1.kind F hF _ (plan.1.measurable_vector.comp hh))
      _ (measurable_paddedObservedHistory plan.1 F hF history hh)

noncomputable def ActionProgram.paddedFinalFrame (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) →
      PaddedHistory E d n Ω → ExposureFrame (Coordinates d) E
  | 0, _, _, _, _, _, F, _ => F
  | n + 1, _, _, _, _, plan, F, history =>
    paddedFinalFrame d n plan.2 (paddedFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (paddedObservedHistory plan.1 F history)

theorem ActionProgram.paddedFinalFrame_measurable (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) :
    ExposureFrame.MeasurableFamily (plan.paddedFinalFrame d n F history) := by
  induction n generalizing H Ω with
  | zero => exact hF
  | succ n ih =>
    exact ih plan.2 _ (measurable_paddedFrameNext plan.1.kind F hF _ (plan.1.measurable_vector.comp hh))
      _ (measurable_paddedObservedHistory plan.1 F hF history hh)

end RandomizedFO2003.Rotations
