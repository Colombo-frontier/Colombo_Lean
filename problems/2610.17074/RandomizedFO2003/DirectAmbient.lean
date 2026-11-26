import RandomizedFO2003.PaddedAmbient

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def ambientFrameNext {m : ℕ} {Ω : Type u} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (x : Ω → E)
    (p : (Ω × E) × E) : ExposureFrame (Coordinates m) E :=
  (F p.1.1).paddedNext kind (x p.1.1) p.1.2
    (Spherical.projectedDirection ((F p.1.1).innovationEmbedding kind) p.2)

noncomputable def ambientObservedHistory {m : ℕ} {H Ω : Type u} [MeasurableSpace H]
    (request : ExposureRequest H E) (F : Ω → ExposureFrame (Coordinates (m + 1)) E)
    (history : Ω → H) (p : (Ω × E) × E) : H × E :=
  (history p.1.1, (F p.1.1).exposedValue request.kind (request.vector (history p.1.1))
    (Spherical.projectedDirection ((F p.1.1).innovationEmbedding request.kind) p.2))

theorem measurable_ambientFrameNext {m : ℕ} {Ω : Type u} [MeasurableSpace Ω] (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (hF : ExposureFrame.MeasurableFamily F)
    (x : Ω → E) (hx : Measurable x) : ExposureFrame.MeasurableFamily (ambientFrameNext kind F x) :=
  (measurable_paddedFrameNext kind F hF x hx).comp
    (ambientDirectionStep_preserving (0 : Measure (Ω × E)) kind
      (fun p => F p.1) (hF.comp measurable_fst)).measurable

theorem measurable_ambientObservedHistory {m : ℕ} {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]
    (request : ExposureRequest H E) (F : Ω → ExposureFrame (Coordinates (m + 1)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    Measurable (ambientObservedHistory request F history) :=
  (measurable_paddedObservedHistory request F hF history hh).comp
    (ambientDirectionStep_preserving (0 : Measure (Ω × E)) request.kind
      (fun p => F p.1) (hF.comp measurable_fst)).measurable

/-- Direct recursion retains all ambient input vectors, so that its information
spaces can be compared with their spans without discarding sampled vectors. -/
noncomputable def ActionProgram.directAmbientTranscript (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) →
      AmbientPairHistory E n Ω → ActionHistory E n H
  | 0, _, _, _, _, _, _, history => history
  | n + 1, _, _, _, _, plan, F, history =>
    directAmbientTranscript d n plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history)

omit [BorelSpace E] in
theorem ActionProgram.directAmbientTranscript_map (d n : ℕ) {H Ω Ω' : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] [MeasurableSpace Ω'] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (f : Ω' → Ω) :
    plan.directAmbientTranscript d n (F ∘ f) (history ∘ f) =
      plan.directAmbientTranscript d n F history ∘ AmbientPairHistory.map E n f := by
  induction n generalizing H Ω Ω' with
  | zero => rfl
  | succ n ih =>
    exact ih plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history) (Prod.map (Prod.map f id) id)

omit [BorelSpace E] in
/-- Keeping the original ambient history agrees pointwise with the simulation
already connected to the actual Haar-driven transcript. -/
theorem ActionProgram.directAmbientTranscript_eq (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) :
    plan.directAmbientTranscript d n F history = plan.paddedAmbientTranscript d n F history := by
  induction n generalizing H Ω with
  | zero => rfl
  | succ n ih =>
    let nextF := paddedFrameNext plan.1.kind F (plan.1.vector ∘ history)
    let nextH := paddedObservedHistory plan.1 F history
    let step := ambientDirectionStep plan.1.kind (fun p : Ω × E => F p.1)
    change plan.2.directAmbientTranscript d n (nextF ∘ step) (nextH ∘ step) = _
    rw [plan.2.directAmbientTranscript_map d n nextF nextH step, ih plan.2 nextF nextH]
    rfl

theorem ActionProgram.directAmbientTranscript_measurable (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) : Measurable (plan.directAmbientTranscript d n F history) := by
  rw [plan.directAmbientTranscript_eq d n F history]
  exact plan.paddedAmbientTranscript_measurable d n F hF history hh

theorem ActionProgram.directAmbientTranscript_law (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    (μ.prod (haarLaw (Coordinates (d + n)))).map
      (fun p => plan.run n ((F p.1).operator p.2) (history p.1)) =
    (ambientPairHistoryLaw E n μ).map (plan.directAmbientTranscript d n F history) := by
  rw [plan.directAmbientTranscript_eq d n F history]
  exact plan.paddedAmbientTranscript_law d n μ F hF history hh

noncomputable def ActionProgram.directAmbientFinalFrame (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) →
      AmbientPairHistory E n Ω → ExposureFrame (Coordinates d) E
  | 0, _, _, _, _, _, F, _ => F
  | n + 1, _, _, _, _, plan, F, history =>
    directAmbientFinalFrame d n plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history)

noncomputable def ActionProgram.directAmbientBound (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) → (Ω → Submodule ℝ E) →
      AmbientPairHistory E n Ω → Submodule ℝ E
  | 0, _, _, _, _, _, _, _, W => W
  | n + 1, _, _, _, _, plan, F, history, W =>
    directAmbientBound d n plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history)
      (fun p => W p.1.1 ⊔ plan.1.kind.latentAddition (plan.1.vector (history p.1.1)) p.1.2 p.2)

/-- Every normalization needed by the padded information-space proof is
nonzero along this particular finite execution. -/
noncomputable def ActionProgram.directAmbientGood (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) → AmbientPairHistory E n Ω → Prop
  | 0, _, _, _, _, _, _, _, _ => True
  | n + 1, _, _, _, _, plan, F, history, p =>
    let q := AmbientPairHistory.seed E n p
    (F q.1.1).latent.toContinuousLinearMap.adjoint q.1.2 ≠ 0 ∧
    ((F q.1.1).innovationEmbedding plan.1.kind).toContinuousLinearMap.adjoint q.2 ≠ 0 ∧
    directAmbientGood d n plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history) p

end RandomizedFO2003.Rotations
