import RandomizedFO2003.MarkedDepth

namespace RandomizedFO2003.SpectralCoordinates

noncomputable def continuousDiagonal {J : ℕ} (K : Fin J → ℕ) (node : Fin J → ℝ) :
    BlockSpace K →L[ℝ] BlockSpace K :=
  ⟨diagonal K node, (diagonal K node).continuous_of_finiteDimensional⟩

theorem shortKrylovSpace_mono {J : ℕ} (K : Fin J → ℕ) (u : BlockSpace K)
    (node : Fin J → ℝ) {a b : ℕ} (hab : a ≤ b) :
    shortKrylovSpace K u node a ≤ shortKrylovSpace K u node b := by
  rw [shortKrylovSpace_eq_powerKrylovSpace, shortKrylovSpace_eq_powerKrylovSpace]
  exact powerKrylovSpace_mono _ _ hab

end RandomizedFO2003.SpectralCoordinates

namespace RandomizedFO2003.Rotations

open MeasureTheory SpectralCoordinates

universe u

/-- The concrete full strategy obeys the short Krylov bound with its actual
authorization count. The earlier legality premise has been discharged. -/
theorem MarkedProgram.selectedQueries_spectral {J : ℕ} (K : Fin J → ℕ) (node : Fin J → ℝ)
    (d t : ℕ) {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]
    (plan : MarkedProgram (BlockSpace K) t H) (mark : H → BlockSpace K) (hm : Measurable mark)
    (F : Ω → ExposureFrame (Coordinates (d + markedActionCount t)) (BlockSpace K)) (history : Ω → H)
    (p : AmbientPairHistory (BlockSpace K) (markedActionCount t) Ω)
    (hsupport : (F (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p)).KnownSupport)
    (hknown : embeddingComplement (F (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p)).latent = ⊥)
    (hgood : (plan.compile (continuousDiagonal K node) t mark hm).directAmbientGood
      d (markedActionCount t) F history p) :
    let transcript := (plan.compile (continuousDiagonal K node) t mark hm).directAmbientTranscript
      d (markedActionCount t) F history p
    ∀ v ∈ (plan.compile (continuousDiagonal K node) t mark hm).selectQueries (markedActionCount t) transcript,
      v ∈ shortKrylovSpace K (mark (history (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p)))
        node (markedDepth t (plan.authorizationTrace t transcript) 0) ⊔
        multiStartKrylovSpace K node (AmbientPairHistory.starts (BlockSpace K) (markedActionCount t) p) := by
  have hlegal := plan.ambientLegal d t (continuousDiagonal K node) mark hm F history (fun _ => ⊥)
    p hsupport (by rw [hknown]) hgood
  apply (plan.compile (continuousDiagonal K node) t mark hm).selectedQueries_spectralKrylov K node
    d (markedActionCount t) _ (plan.ambientOperations (continuousDiagonal K node) d t mark hm F history p)
    _ F history p hsupport hknown hlegal _ hgood
  rw [plan.ambientOperations_eq]
  exact le_rfl

theorem MarkedProgram.selectedQueries_ae_spectral {J : ℕ} (K : Fin J → ℕ) (node : Fin J → ℝ)
    (d t : ℕ) {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : MarkedProgram (BlockSpace K) t H)
    (mark : H → BlockSpace K) (hm : Measurable mark)
    (F : Ω → ExposureFrame (Coordinates (d + markedActionCount t)) (BlockSpace K))
    (hF : ExposureFrame.MeasurableFamily F) (hsupport : ∀ ω, (F ω).KnownSupport)
    (hknown : ∀ ω, embeddingComplement (F ω).latent = ⊥) (history : Ω → H) (hh : Measurable history) :
    ∀ᵐ p ∂ambientPairHistoryLaw (BlockSpace K) (markedActionCount t) μ,
      let transcript := (plan.compile (continuousDiagonal K node) t mark hm).directAmbientTranscript
        d (markedActionCount t) F history p
      ∀ v ∈ (plan.compile (continuousDiagonal K node) t mark hm).selectQueries (markedActionCount t) transcript,
        v ∈ shortKrylovSpace K (mark (history (AmbientPairHistory.seed (BlockSpace K) (markedActionCount t) p)))
          node (markedDepth t (plan.authorizationTrace t transcript) 0) ⊔
          multiStartKrylovSpace K node (AmbientPairHistory.starts (BlockSpace K) (markedActionCount t) p) := by
  filter_upwards [(plan.compile (continuousDiagonal K node) t mark hm).directAmbientGood_ae
    d (markedActionCount t) μ F hF history hh] with p hp
  exact plan.selectedQueries_spectral K node d t mark hm F history p (hsupport _) (hknown _) hp

end RandomizedFO2003.Rotations
