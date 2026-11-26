import RandomizedFO2003.AmbientSpectralKrylov

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A matrix response can request only the spectral matrix applied to the
latent vector returned by the immediately preceding inverse query. -/
noncomputable def matrixResponseRequest {H : Type u} [MeasurableSpace H]
    (A : E →L[ℝ] E) : ExposureRequest (H × E) E :=
  ⟨.response, fun h => A h.2, A.continuous.measurable.comp measurable_snd⟩

/-- One concrete strengthened matrix-oracle round: return `U†x`, then
`U A U†x`, with a policy reading the complete preceding ordinary transcript. -/
noncomputable def ActionProgram.matrixRound {H : Type u} [MeasurableSpace H] {n : ℕ}
    (A : E →L[ℝ] E) (x : H → E) (hx : Measurable x)
    (rest : ActionProgram E n ((H × E) × E)) : ActionProgram E (n + 2) H :=
  (⟨.query, x, hx⟩, matrixResponseRequest A, rest)

theorem ActionProgram.matrixRound_run {H : Type u} [MeasurableSpace H] {n : ℕ}
    (A : E →L[ℝ] E) (x : H → E) (hx : Measurable x)
    (rest : ActionProgram E n ((H × E) × E)) (U : E →L[ℝ] E) (h : H) :
    (ActionProgram.matrixRound A x hx rest).run (n + 2) U h =
      rest.run n U ((h, U.adjoint (x h)), U (A (U.adjoint (x h)))) := rfl

omit [BorelSpace E] [MeasurableSpace E] in
/-- The inverse value needed by a following matrix request is already in the
new cumulative space. This holds even at zero projections. -/
theorem ExposureFrame.KnownSupport.ambientQueryValue_mem {m : ℕ}
    {F : ExposureFrame (Coordinates (m + 1)) E} (hF : F.KnownSupport)
    (W : Submodule ℝ E) (hW : embeddingComplement F.latent ≤ W) (x g : E) :
    F.exposedValue .query x (Spherical.projectedDirection F.latent g) ∈
      W ⊔ Submodule.span ℝ {g} := by
  change F.known.adjoint x + ‖F.physical.toContinuousLinearMap.adjoint x‖ •
    F.latent (Spherical.projectedDirection F.latent g) ∈ _
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (hW (hF.latent x))
  · apply Submodule.smul_mem
    exact (sup_le_sup_right hW _) (projectedDirection_mem_sup F.latent g)

/-- A concrete matrix request satisfies the legality premise from the new
chronological theorem; it is not an assumed arbitrary forward response. -/
theorem matrixResponseRequest_legal {m : ℕ} {H : Type u} [MeasurableSpace H]
    (A : E →L[ℝ] E) (u : E) (F : ExposureFrame (Coordinates (m + 1)) E)
    (hF : F.KnownSupport) (W : Submodule ℝ E) (hW : embeddingComplement F.latent ≤ W)
    (h : H) (x g : E) :
    LatentOperation.matrix.Legal A.toLinearMap u (W ⊔ Submodule.span ℝ {g})
      ((matrixResponseRequest A).vector
        (h, F.exposedValue .query x (Spherical.projectedDirection F.latent g))) := by
  exact ⟨_, hF.ambientQueryValue_mem W hW x g, rfl⟩

/-- A fixed forward slot implements a history-dependent authorization decision.
Before authorization the actual requested vector is zero. -/
noncomputable def authorizedMarkRequest {H : Type u} [MeasurableSpace H]
    (u : E) (authorized : H → Bool) (ha : Measurable authorized) : ExposureRequest H E :=
  ⟨.response, fun h => if authorized h = true then u else 0,
    measurable_const.ite (ha (measurableSet_singleton true)) measurable_const⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem authorizedMarkRequest_legal {H : Type u} [MeasurableSpace H]
    (u : E) (authorized : H → Bool) (ha : Measurable authorized)
    (A : Module.End ℝ E) (W : Submodule ℝ E) (h : H) :
    (LatentOperation.mark (authorized h)).Legal A u W
      ((authorizedMarkRequest u authorized ha).vector h) := by
  cases hb : authorized h <;>
    simp [authorizedMarkRequest, hb, LatentOperation.Legal, Submodule.mem_span_singleton_self]

omit [BorelSpace E] in
theorem authorizedMarkRequest_value {H : Type u} [MeasurableSpace H]
    (u : E) (authorized : H → Bool) (ha : Measurable authorized) (U : E →L[ℝ] E) (h : H) :
    ExposureKind.response.action U ((authorizedMarkRequest u authorized ha).vector h) =
      if authorized h = true then U u else 0 := by
  cases hb : authorized h <;> simp [ExposureKind.action, authorizedMarkRequest, hb]

end RandomizedFO2003.Rotations
