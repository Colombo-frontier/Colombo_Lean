import RandomizedFO2003.AmbientHistory
import RandomizedFO2003.ActionProbability

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def ExposureFrame.innovationEmbedding {m : ℕ} (F : ExposureFrame (Coordinates m) E)
    (kind : ExposureKind) : Coordinates m →ₗᵢ[ℝ] E :=
  match kind with
  | .query => F.latent
  | .response => F.physical

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem ExposureFrame.MeasurableFamily.innovationEmbedding {m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {F : Ω → ExposureFrame (Coordinates m) E} (hF : ExposureFrame.MeasurableFamily F) (kind : ExposureKind) :
    Measurable (fun ω => ((F ω).innovationEmbedding kind).toContinuousLinearMap) := by
  cases kind with
  | query => exact hF.latent
  | response => exact hF.physical

noncomputable def ambientDirectionStep {m : ℕ} {Ω : Type u}
    (kind : ExposureKind) (F : Ω → ExposureFrame (Coordinates (m + 1)) E)
    (p : Ω × E) : Ω × Coordinates (m + 1) :=
  (p.1, Spherical.projectedDirection ((F p.1).innovationEmbedding kind) p.2)

theorem ambientDirectionStep_preserving {m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (hF : ExposureFrame.MeasurableFamily F) :
    MeasurePreserving (ambientDirectionStep kind F) (μ.prod (Spherical.sphereLaw E))
      (μ.prod (Spherical.sphereLaw (Coordinates (m + 1)))) := by
  letI : Nontrivial (Coordinates (m + 1)) := ⟨⟨firstDirection m, 0, firstDirection_ne_zero m⟩⟩
  exact Spherical.projectedDirection_product μ (fun ω => (F ω).innovationEmbedding kind)
    (hF.innovationEmbedding kind)

/-- Generate the changing-coordinate exposure history from independent vectors
in the one fixed ambient space. -/
noncomputable def ExposureProgram.ambientSample (d : ℕ) : (n : ℕ) → {Ω : Type u} → [MeasurableSpace Ω] →
    ExposureProgram E d n Ω → (Ω → ExposureFrame (Coordinates (d + n)) E) →
      ActionHistory E n Ω → ExposureHistory d n Ω
  | 0, _, _, _, _ => id
  | n + 1, _, _, plan, F =>
    ambientSample d n plan.2 (fun p => (F p.1).standardNext plan.1.kind (plan.1.vector p.1) p.2) ∘
      ActionHistory.map E n (ambientDirectionStep plan.1.kind F)

/-- The entire ambient-vector simulation has exactly the previously proved
product sphere exposure law, for arbitrary measurable adaptive requests. -/
theorem ExposureProgram.ambientSample_preserving (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ExposureProgram E d n Ω)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F) :
    MeasurePreserving (plan.ambientSample d n F) (ambientHistoryLaw E n μ) (exposureHistoryLaw d n μ) := by
  induction n generalizing Ω with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) := Measure.prod.instSFinite
    exact (ih (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) plan.2 _
      (hF.standardNext plan.1.kind plan.1.measurable_vector)).comp
      (ActionHistory.map_preserving n _ _ _ (ambientDirectionStep_preserving μ plan.1.kind F hF))

/-- Every full-transcript policy driven by a genuine Haar rotation admits a
simulation using a fixed ambient sphere independently at each exposure. The
seed, which may contain an entire independent marked-vector tuple, is retained. -/
theorem ActionProgram.ambient_transcript_representation (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ActionProgram (Coordinates (d + n)) n Ω) :
    ∃ transcript : ActionHistory (Coordinates (d + n)) n Ω → ActionHistory (Coordinates (d + n)) n Ω,
      Measurable transcript ∧
      (μ.prod (haarLaw (Coordinates (d + n)))).map
        (fun p => plan.run n (p.2 : Coordinates (d + n) →L[ℝ] Coordinates (d + n)) p.1) =
      (ambientHistoryLaw (Coordinates (d + n)) n μ).map transcript := by
  let F : Ω → ExposureFrame (Coordinates (d + n)) (Coordinates (d + n)) := fun _ => .initial
  have hF : ExposureFrame.MeasurableFamily F := ExposureFrame.measurable_initial
  let compiled := plan.compile d n F hF id measurable_id
  let readout := plan.historyMap d n F id
  have hread : Measurable readout := plan.historyMap_measurable d n F hF id measurable_id
  let sample := compiled.ambientSample d n F
  have hsample := compiled.ambientSample_preserving d n μ F hF
  refine ⟨readout ∘ sample, hread.comp hsample.measurable, ?_⟩
  rw [← Measure.map_map hread hsample.measurable, hsample.map_eq]
  have hp := plan.exposureCoordinates_preserving d n μ F hF id measurable_id
  have hf : MeasurePreserving Prod.fst
      (((exposureHistoryLaw d n μ).map readout).prod (haarLaw (Coordinates d)))
      ((exposureHistoryLaw d n μ).map readout) := ⟨measurable_fst, by simp⟩
  have heq := (hf.comp hp).map_eq
  convert heq using 1
  congr 1
  funext p
  exact congrArg (fun A => plan.run n A p.1) (ExposureFrame.initial_operator p.2).symm

end RandomizedFO2003.Rotations
