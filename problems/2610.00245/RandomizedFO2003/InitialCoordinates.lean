import RandomizedFO2003.MarkedProbability

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def initialCoordinates (n : ℕ) (h : Module.finrank ℝ E = n) : E ≃ₗᵢ[ℝ] Coordinates n := by
  subst n
  exact (stdOrthonormalBasis ℝ E).repr

omit [MeasurableSpace E] [BorelSpace E] in
theorem initial_reindex_latentComplement {n : ℕ} (V : E ≃ₗᵢ[ℝ] Coordinates n) :
    embeddingComplement ((ExposureFrame.initial : ExposureFrame E E).reindex V).latent = ⊥ := by
  rw [ExposureFrame.reindex, embeddingComplement_reindex, initial_latentComplement]

/-- The initial coordinate frame is only a change of basis: its transcript law
is precisely the law of the actual Haar orthogonal operator on `E`. -/
theorem ActionProgram.initial_coordinate_law (d n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (plan : ActionProgram E n H)
    (V : E ≃ₗᵢ[ℝ] Coordinates (d + n)) :
    (μ.prod (haarLaw E)).map (fun p => plan.run n (p.2 : E →L[ℝ] E) p.1) =
      (μ.prod (haarLaw (Coordinates (d + n)))).map
        (fun p => plan.run n (((ExposureFrame.initial : ExposureFrame E E).reindex V).operator p.2) p.1) := by
  let F := fun _ : H => (ExposureFrame.initial : ExposureFrame E E).reindex V
  have hF : ExposureFrame.MeasurableFamily F := ExposureFrame.measurable_initial.reindex V
  let runCoordinates := fun p : H × Rotation (Coordinates (d + n)) =>
    plan.run n ((F p.1).operator p.2) p.1
  have hrun : Measurable runCoordinates := plan.run_measurable d n F hF id measurable_id
  have hp := (MeasurePreserving.id μ).prod (rotationCoordinates_preserving V)
  have ht : MeasurePreserving runCoordinates (μ.prod (haarLaw (Coordinates (d + n))))
      ((μ.prod (haarLaw (Coordinates (d + n)))).map runCoordinates) := ⟨hrun, rfl⟩
  have heq : runCoordinates ∘ Prod.map id (rotationCoordinates V) =
      fun p : H × Rotation E => plan.run n (p.2 : E →L[ℝ] E) p.1 := by
    funext p
    dsimp only [Function.comp_apply, Prod.map_apply, id_eq, runCoordinates, F]
    change plan.run n (((ExposureFrame.initial : ExposureFrame E E).reindex V).operator
      (rotationCoordinates V p.2)) p.1 = _
    rw [ExposureFrame.reindex_operator, ExposureFrame.initial_operator]
  have h := (ht.comp hp).map_eq
  rw [heq] at h
  exact h

end RandomizedFO2003.Rotations
