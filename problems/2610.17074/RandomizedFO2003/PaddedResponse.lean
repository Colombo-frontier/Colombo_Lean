import RandomizedFO2003.FrameSupport
import RandomizedFO2003.FrameProbability

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]

/-- An already-known response may expose an independent auxiliary vector
internally. The actual requested response is still returned unchanged. -/
noncomputable def ExposureFrame.paddedResponse (F : ExposureFrame S E) (y auxiliary : E) : E := by
  classical
  exact if F.latent.toContinuousLinearMap.adjoint y = 0 then auxiliary else y

theorem ExposureFrame.paddedResponse_ne_zero (F : ExposureFrame S E) (y auxiliary : E)
    (ha : F.latent.toContinuousLinearMap.adjoint auxiliary ≠ 0) :
    F.latent.toContinuousLinearMap.adjoint (F.paddedResponse y auxiliary) ≠ 0 := by
  classical
  by_cases hy : F.latent.toContinuousLinearMap.adjoint y = 0
  · simpa [ExposureFrame.paddedResponse, hy] using ha
  · simp [ExposureFrame.paddedResponse, hy]

/-- Padding preserves the complete vector returned for the original request,
including the branch where that vector was already determined by the history. -/
theorem ExposureFrame.response_vector_padded (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y auxiliary : E) (R : Rotation S) :
    F.operator R y = F.known y + ‖F.latent.toContinuousLinearMap.adjoint y‖ •
      F.physical (F.responseSplit e (F.paddedResponse y auxiliary) R).1 := by
  by_cases hy : F.latent.toContinuousLinearMap.adjoint y = 0
  · simp [ExposureFrame.operator, hy]
  · simpa [ExposureFrame.paddedResponse, hy] using F.response_vector e he y R

/-- Both branches add only the requested vector or the independent auxiliary
vector to the previous latent information space. -/
theorem ExposureFrame.paddedResponse_span (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y auxiliary : E) (ξ : S) (ha : F.latent.toContinuousLinearMap.adjoint auxiliary ≠ 0) :
    embeddingComplement (F.afterResponse e (F.paddedResponse y auxiliary) ξ).latent ≤
      embeddingComplement F.latent ⊔ Submodule.span ℝ {y, auxiliary} := by
  apply (F.afterResponse_span e he _ ξ (F.paddedResponse_ne_zero y auxiliary ha)).trans
  apply sup_le_sup_left
  apply Submodule.span_mono
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  classical
  by_cases hy : F.latent.toContinuousLinearMap.adjoint y = 0 <;>
    simp [ExposureFrame.paddedResponse, hy]

theorem ExposureFrame.paddedResponse_request_mem (F : ExposureFrame S E) (e : S) (he : ‖e‖ = 1)
    (y auxiliary : E) (ξ : S) :
    y ∈ embeddingComplement (F.afterResponse e (F.paddedResponse y auxiliary) ξ).latent := by
  by_cases hy : F.latent.toContinuousLinearMap.adjoint y = 0
  · change y ∈ embeddingComplement (F.latent.comp
      (complementEmbedding e (householder (e - F.responseDirection e (F.paddedResponse y auxiliary)))))
    exact embeddingComplement_le_comp F.latent _ ((mem_embeddingComplement F.latent y).mpr hy)
  · simpa [ExposureFrame.paddedResponse, hy] using F.afterResponse_request_mem e he y ξ

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S]

theorem ExposureFrame.MeasurableFamily.paddedResponse {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → ExposureFrame S E} (hF : ExposureFrame.MeasurableFamily F)
    {y auxiliary : Ω → E} (hy : Measurable y) (ha : Measurable auxiliary) :
    Measurable (fun ω => (F ω).paddedResponse (y ω) (auxiliary ω)) := by
  classical
  have hz : Measurable (fun ω => (F ω).latent.toContinuousLinearMap.adjoint (y ω)) :=
    measurable_operator_apply (measurable_operator_adjoint hF.latent) hy
  exact Measurable.ite (hz (measurableSet_singleton 0)) ha hy

/-- An independent auxiliary sphere vector makes the internal response
nondegenerate almost surely, uniformly over the whole previous history. -/
theorem paddedResponse_ae_nonzero [Nontrivial S] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (F : Ω → ExposureFrame S E) (hF : ExposureFrame.MeasurableFamily F)
    (y : Ω → E) (hy : Measurable y) :
    ∀ᵐ p ∂μ.prod (Spherical.sphereLaw E),
      (F p.1).latent.toContinuousLinearMap.adjoint ((F p.1).paddedResponse (y p.1) p.2) ≠ 0 := by
  have ha : Measurable (fun p : Ω × E =>
      (F p.1).latent.toContinuousLinearMap.adjoint ((F p.1).paddedResponse (y p.1) p.2)) :=
    measurable_operator_apply ((measurable_operator_adjoint hF.latent).comp measurable_fst)
      ((hF.comp measurable_fst).paddedResponse (hy.comp measurable_fst) measurable_snd)
  apply (Measure.ae_prod_iff_ae_ae (ha (measurableSet_singleton 0)).compl).mpr
  exact Filter.Eventually.of_forall (fun ω =>
    (Spherical.ae_adjoint_ne_zero (F ω).latent).mono (fun a ha => (F ω).paddedResponse_ne_zero (y ω) a ha))

end RandomizedFO2003.Rotations
