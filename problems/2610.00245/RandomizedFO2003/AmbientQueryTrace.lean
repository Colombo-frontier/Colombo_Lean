import RandomizedFO2003.DirectAmbientInformation

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

def ActionHistory.seed (E : Type) : (n : ℕ) → {H : Type u} → ActionHistory E n H → H
  | 0, _, p => p
  | n + 1, _, p => (seed E n p).1

theorem ActionHistory.seed_measurable {E : Type} [MeasurableSpace E] (n : ℕ)
    {H : Type u} [MeasurableSpace H] : Measurable (ActionHistory.seed E n (H := H)) := by
  induction n generalizing H with
  | zero => exact measurable_id
  | succ n ih => exact (ih (H := H × E)).fst

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- Extract precisely the latent inverse-query answers from the ordinary
transcript. Forward physical responses are not treated as latent vectors. -/
def ActionProgram.selectQueries : (n : ℕ) → {H : Type u} → [MeasurableSpace H] →
    ActionProgram E n H → ActionHistory E n H → List E
  | 0, _, _, _, _ => []
  | n + 1, _, _, plan, p =>
    match plan.1.kind with
    | .query => (ActionHistory.seed E n p).2 :: selectQueries n plan.2 p
    | .response => selectQueries n plan.2 p

theorem ActionProgram.directAmbientTranscript_seed (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (p : AmbientPairHistory E n Ω) :
    ActionHistory.seed E n (plan.directAmbientTranscript d n F history p) =
      history (AmbientPairHistory.seed E n p) := by
  induction n generalizing H Ω with
  | zero => rfl
  | succ n ih =>
    exact congrArg Prod.fst (ih plan.2 (ambientFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (ambientObservedHistory plan.1 F history) p)

/-- The information-space trace is exactly the query subsequence of the
simulated ordinary transcript, rather than an unrelated witness list. -/
theorem ActionProgram.selectQueries_directAmbient (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) (p : AmbientPairHistory E n Ω) :
    plan.selectQueries n (plan.directAmbientTranscript d n F history p) =
      plan.directAmbientQueries d n F history p := by
  induction n generalizing H Ω with
  | zero => rfl
  | succ n ih =>
    let nextF := ambientFrameNext plan.1.kind F (plan.1.vector ∘ history)
    let nextH := ambientObservedHistory plan.1 F history
    have hs := plan.2.directAmbientTranscript_seed d n nextF nextH p
    have ht := ih plan.2 nextF nextH p
    cases hk : plan.1.kind with
    | query =>
      change (match plan.1.kind with
        | .query => (ActionHistory.seed E n (plan.2.directAmbientTranscript d n nextF nextH p)).2 ::
            plan.2.selectQueries n (plan.2.directAmbientTranscript d n nextF nextH p)
        | .response => plan.2.selectQueries n (plan.2.directAmbientTranscript d n nextF nextH p)) = _
      rw [hk, hs, ht]
      simp only [ActionProgram.directAmbientQueries, nextF, nextH, hk]
    | response =>
      simpa only [ActionProgram.selectQueries, ActionProgram.directAmbientTranscript,
        ActionProgram.directAmbientQueries, nextF, nextH, hk] using ht

variable [BorelSpace E]

/-- Under the independent ambient law all actual inverse-query answers in the
simulated transcript satisfy the cumulative information-space bound almost surely. -/
theorem ActionProgram.selectedQueries_ae_bound (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (hsupport : ∀ ω, (F ω).KnownSupport)
    (history : Ω → H) (hh : Measurable history) (W : Ω → Submodule ℝ E)
    (hW : ∀ ω, embeddingComplement (F ω).latent ≤ W ω) :
    ∀ᵐ p ∂ambientPairHistoryLaw E n μ,
      ∀ v ∈ plan.selectQueries n (plan.directAmbientTranscript d n F history p),
        v ∈ plan.directAmbientBound d n F history W p := by
  filter_upwards [plan.directAmbientGood_ae d n μ F hF history hh] with p hp
  rw [plan.selectQueries_directAmbient d n F history p]
  exact plan.directAmbientQueries_mem d n F history W p
    (hsupport _) (hW _) hp

omit [BorelSpace E] [MeasurableSpace E] in
@[simp] theorem initial_latentComplement :
    embeddingComplement (ExposureFrame.initial : ExposureFrame E E).latent = ⊥ := by
  ext x
  rw [mem_embeddingComplement, Submodule.mem_bot]
  change (LinearIsometry.id : E →ₗᵢ[ℝ] E).toContinuousLinearMap.adjoint
    ((LinearIsometry.id : E →ₗᵢ[ℝ] E) x) = 0 ↔ x = 0
  rw [embedding_adjoint_self]

/-- A genuine Haar-driven full-transcript policy is represented by independent
ambient pairs, and all of its latent query answers obey the cumulative span
recursion almost surely. No initial latent information is assumed. -/
theorem ActionProgram.haar_ambient_information (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ActionProgram (Coordinates (d + n)) n Ω) :
    Measurable (plan.directAmbientTranscript d n (fun _ => .initial) id) ∧
    (μ.prod (haarLaw (Coordinates (d + n)))).map
      (fun p => plan.run n (p.2 : Coordinates (d + n) →L[ℝ] Coordinates (d + n)) p.1) =
      (ambientPairHistoryLaw (Coordinates (d + n)) n μ).map
        (plan.directAmbientTranscript d n (fun _ => .initial) id) ∧
    (∀ᵐ p ∂ambientPairHistoryLaw (Coordinates (d + n)) n μ,
      ∀ v ∈ plan.selectQueries n (plan.directAmbientTranscript d n (fun _ => .initial) id p),
        v ∈ plan.directAmbientBound d n (fun _ => .initial) id (fun _ => ⊥) p) := by
  have hF : ExposureFrame.MeasurableFamily (fun _ : Ω =>
      (ExposureFrame.initial : ExposureFrame (Coordinates (d + n)) (Coordinates (d + n)))) :=
    ExposureFrame.measurable_initial
  refine ⟨plan.directAmbientTranscript_measurable d n _ hF id measurable_id, ?_, ?_⟩
  · simpa only [ExposureFrame.initial_operator, id_eq] using
      plan.directAmbientTranscript_law d n μ _ hF id measurable_id
  · exact plan.selectedQueries_ae_bound d n μ _ hF (fun _ => ExposureFrame.initial_knownSupport)
      id measurable_id (fun _ => ⊥) (fun _ => by rw [initial_latentComplement])

end RandomizedFO2003.Rotations
