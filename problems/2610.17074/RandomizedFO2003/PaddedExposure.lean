import RandomizedFO2003.PaddedResponse
import RandomizedFO2003.AmbientExposure

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type} {Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

noncomputable def ExposureFrame.internalRequest {n : ℕ} (F : ExposureFrame (Coordinates (n + 1)) E)
    (kind : ExposureKind) (x auxiliary : E) : E :=
  match kind with
  | .query => x
  | .response => F.paddedResponse x auxiliary

theorem ExposureFrame.MeasurableFamily.internalRequest {n : ℕ}
    {F : Ω → ExposureFrame (Coordinates (n + 1)) E} (hF : ExposureFrame.MeasurableFamily F)
    (kind : ExposureKind) {x auxiliary : Ω → E} (hx : Measurable x) (ha : Measurable auxiliary) :
    Measurable (fun ω => (F ω).internalRequest kind (x ω) (auxiliary ω)) := by
  cases kind with
  | query => exact hx
  | response => exact hF.paddedResponse hx ha

noncomputable def ExposureFrame.paddedNext {n : ℕ} (F : ExposureFrame (Coordinates (n + 1)) E)
    (kind : ExposureKind) (x auxiliary : E) (ξ : Coordinates (n + 1)) : ExposureFrame (Coordinates n) E :=
  F.standardNext kind (F.internalRequest kind x auxiliary) ξ

/-- Only inverse queries create an independent latent start. Forward responses
add the known latent request, or an auxiliary start for a degenerate request. -/
def ExposureKind.latentAddition (kind : ExposureKind) (x auxiliary g : E) : Submodule ℝ E :=
  match kind with
  | .query => Submodule.span ℝ {g}
  | .response => Submodule.span ℝ {x, auxiliary}

noncomputable def paddedTransition {n : ℕ} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (n + 1)) E) (x auxiliary : Ω → E) :=
  standardTransition kind F (fun ω => (F ω).internalRequest kind (x ω) (auxiliary ω))

theorem paddedTransition_preserving {n : ℕ} (μ : Measure Ω) [SFinite μ]
    (kind : ExposureKind) (F : Ω → ExposureFrame (Coordinates (n + 1)) E)
    (hF : ExposureFrame.MeasurableFamily F) (x auxiliary : Ω → E)
    (hx : Measurable x) (ha : Measurable auxiliary) :
    MeasurePreserving (paddedTransition kind F x auxiliary)
      (μ.prod (haarLaw (Coordinates (n + 1))))
      ((μ.prod (Spherical.sphereLaw (Coordinates (n + 1)))).prod (haarLaw (Coordinates n))) :=
  standardTransition_preserving μ kind F hF _ (hF.internalRequest kind hx ha)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem paddedTransition_operator {n : ℕ} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (n + 1)) E) (x auxiliary : Ω → E)
    (p : Ω × Rotation (Coordinates (n + 1))) :
    (F p.1).operator p.2 =
      ((F (paddedTransition kind F x auxiliary p).1.1).paddedNext kind
        (x (paddedTransition kind F x auxiliary p).1.1) (auxiliary (paddedTransition kind F x auxiliary p).1.1)
        (paddedTransition kind F x auxiliary p).1.2).operator (paddedTransition kind F x auxiliary p).2 :=
  standardTransition_operator kind F _ p

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
/-- Internal padding preserves the original action, so the actual algorithm's
transcript uses the same readout formula as before. -/
theorem paddedTransition_value {n : ℕ} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (n + 1)) E) (x auxiliary : Ω → E)
    (p : Ω × Rotation (Coordinates (n + 1))) :
    kind.action ((F p.1).operator p.2) (x p.1) =
      (F p.1).exposedValue kind (x p.1) (paddedTransition kind F x auxiliary p).1.2 := by
  cases kind with
  | query => exact (F p.1).query_vector _ (norm_firstDirection n) (x p.1) p.2
  | response => exact (F p.1).response_vector_padded _ (norm_firstDirection n) (x p.1) (auxiliary p.1) p.2

theorem ExposureFrame.MeasurableFamily.paddedNext {n : ℕ}
    {F : Ω → ExposureFrame (Coordinates (n + 1)) E} (hF : ExposureFrame.MeasurableFamily F)
    (kind : ExposureKind) {x auxiliary : Ω → E} (hx : Measurable x) (ha : Measurable auxiliary) :
    ExposureFrame.MeasurableFamily (fun p : Ω × Coordinates (n + 1) =>
      (F p.1).paddedNext kind (x p.1) (auxiliary p.1) p.2) :=
  ExposureFrame.MeasurableFamily.standardNext (n := n) (F := F)
    (x := fun ω => (F ω).internalRequest kind (x ω) (auxiliary ω)) hF kind
      (hF.internalRequest kind hx ha)

omit [MeasurableSpace E] [BorelSpace E] in
theorem ExposureFrame.KnownSupport.paddedNext {n : ℕ} {F : ExposureFrame (Coordinates (n + 1)) E}
    (hF : F.KnownSupport) (kind : ExposureKind) (x auxiliary : E) (ξ : Coordinates (n + 1)) :
    (F.paddedNext kind x auxiliary ξ).KnownSupport := hF.standardNext kind _ ξ

omit [MeasurableSpace E] [BorelSpace E] in
/-- A single padded exposure adds only independent ambient vectors and the
requested vector to the latent information space. -/
theorem ExposureFrame.paddedNext_latent_span {n : ℕ} (F : ExposureFrame (Coordinates (n + 1)) E)
    (kind : ExposureKind) (x auxiliary g : E)
    (hg : (F.innovationEmbedding kind).toContinuousLinearMap.adjoint g ≠ 0)
    (ha : F.latent.toContinuousLinearMap.adjoint auxiliary ≠ 0) :
    embeddingComplement (F.paddedNext kind x auxiliary
      (Spherical.projectedDirection (F.innovationEmbedding kind) g)).latent ≤
      embeddingComplement F.latent ⊔ kind.latentAddition x auxiliary g := by
  cases kind with
  | query =>
    change embeddingComplement
      ((F.afterQuery (firstDirection n) x (Spherical.projectedDirection F.latent g)).latent.comp
        (tailCoordinates n).symm.toLinearIsometry) ≤ _
    rw [embeddingComplement_reindex]
    exact F.afterQuery_ambient_span _ (norm_firstDirection n) x g hg
  | response =>
    change embeddingComplement
      ((F.afterResponse (firstDirection n) (F.paddedResponse x auxiliary)
        (Spherical.projectedDirection F.physical g)).latent.comp (tailCoordinates n).symm.toLinearIsometry) ≤ _
    rw [embeddingComplement_reindex]
    exact F.paddedResponse_span _ (norm_firstDirection n) x auxiliary _ ha

end RandomizedFO2003.Rotations
