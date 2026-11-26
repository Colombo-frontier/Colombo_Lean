import RandomizedFO2003.FrameProbability
import RandomizedFO2003.RotationCoordinates

namespace RandomizedFO2003.Rotations

open MeasureTheory

abbrev Coordinates (n : ℕ) := EuclideanSpace ℝ (Fin n)

instance coordinates_sphereLaw_sFinite (n : ℕ) : SFinite (Spherical.sphereLaw (Coordinates n)) := by
  haveI : IsProbabilityMeasure (Spherical.sphereLaw (Coordinates n)) := Spherical.sphereLaw_probability _
  haveI : IsFiniteMeasure (Spherical.sphereLaw (Coordinates n)) := ⟨by simp⟩
  haveI : SigmaFinite (Spherical.sphereLaw (Coordinates n)) := IsFiniteMeasure.toSigmaFinite _
  infer_instance

noncomputable def firstDirection (n : ℕ) : Coordinates (n + 1) := EuclideanSpace.single 0 1

@[simp] theorem norm_firstDirection (n : ℕ) : ‖firstDirection n‖ = 1 := by
  simp [firstDirection]

theorem firstDirection_ne_zero (n : ℕ) : firstDirection n ≠ 0 := by
  intro h
  have := norm_firstDirection n
  simp [h] at this

/-- A fixed coordinate system for the residual space, of dimension one less. -/
noncomputable def tailCoordinates (n : ℕ) :
    (Submodule.span ℝ {firstDirection n})ᗮ ≃ₗᵢ[ℝ] Coordinates n := by
  letI : Fact (Module.finrank ℝ (Coordinates (n + 1)) = n + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton n (firstDirection_ne_zero n)).repr

inductive ExposureKind where
  | query
  | response

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def ExposureFrame.standardNext {n : ℕ} (F : ExposureFrame (Coordinates (n + 1)) E)
    (kind : ExposureKind) (x : E) (ξ : Coordinates (n + 1)) : ExposureFrame (Coordinates n) E :=
  match kind with
  | .query => (F.afterQuery (firstDirection n) x ξ).reindex (tailCoordinates n)
  | .response => (F.afterResponse (firstDirection n) x ξ).reindex (tailCoordinates n)

noncomputable def standardTransition {n : ℕ} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (n + 1)) E) (x : Ω → E)
    (p : Ω × Rotation (Coordinates (n + 1))) : (Ω × Coordinates (n + 1)) × Rotation (Coordinates n) :=
  let q := match kind with
    | .query => frameQueryTransition F (firstDirection n) x p
    | .response => frameResponseTransition F (firstDirection n) x p
  (q.1, rotationCoordinates (tailCoordinates n) q.2)

theorem ExposureFrame.MeasurableFamily.standardNext {n : ℕ}
    {F : Ω → ExposureFrame (Coordinates (n + 1)) E} (hF : ExposureFrame.MeasurableFamily F)
    (kind : ExposureKind) {x : Ω → E} (hx : Measurable x) :
    ExposureFrame.MeasurableFamily (fun p : Ω × Coordinates (n + 1) =>
      (F p.1).standardNext kind (x p.1) p.2) := by
  cases kind with
  | query => exact (hF.afterQuery (firstDirection n) hx).reindex (tailCoordinates n)
  | response => exact (hF.afterResponse (firstDirection n) hx).reindex (tailCoordinates n)

/-- The next direction and smaller Haar rotation are independent of each other
and of the previous history, for either an inverse query or forward response. -/
theorem standardTransition_preserving {n : ℕ} (μ : Measure Ω) [SFinite μ]
    (kind : ExposureKind) (F : Ω → ExposureFrame (Coordinates (n + 1)) E)
    (hF : ExposureFrame.MeasurableFamily F) (x : Ω → E) (hx : Measurable x) :
    MeasurePreserving (standardTransition kind F x) (μ.prod (haarLaw (Coordinates (n + 1))))
      ((μ.prod (Spherical.sphereLaw (Coordinates (n + 1)))).prod (haarLaw (Coordinates n))) := by
  haveI : SFinite (μ.prod (Spherical.sphereLaw (Coordinates (n + 1)))) := Measure.prod.instSFinite
  have hc := (MeasurePreserving.id (μ.prod (Spherical.sphereLaw (Coordinates (n + 1))))).prod
    (rotationCoordinates_preserving (tailCoordinates n))
  cases kind with
  | query => exact hc.comp (frameQueryTransition_preserving μ F hF _ (norm_firstDirection n) x hx)
  | response => exact hc.comp (frameResponseTransition_preserving μ F hF _ (norm_firstDirection n) x hx)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem standardTransition_operator {n : ℕ} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (n + 1)) E) (x : Ω → E)
    (p : Ω × Rotation (Coordinates (n + 1))) :
    (F p.1).operator p.2 =
      ((F (standardTransition kind F x p).1.1).standardNext kind
        (x (standardTransition kind F x p).1.1) (standardTransition kind F x p).1.2).operator
          (standardTransition kind F x p).2 := by
  cases kind with
  | query =>
    change (F p.1).operator p.2 =
      (((F p.1).afterQuery (firstDirection n) (x p.1)
        (frameQueryTransition F (firstDirection n) x p).1.2).reindex (tailCoordinates n)).operator
          (rotationCoordinates (tailCoordinates n) (frameQueryTransition F (firstDirection n) x p).2)
    rw [ExposureFrame.reindex_operator]
    exact frameQueryTransition_operator F _ (norm_firstDirection n) x p
  | response =>
    change (F p.1).operator p.2 =
      (((F p.1).afterResponse (firstDirection n) (x p.1)
        (frameResponseTransition F (firstDirection n) x p).1.2).reindex (tailCoordinates n)).operator
          (rotationCoordinates (tailCoordinates n) (frameResponseTransition F (firstDirection n) x p).2)
    rw [ExposureFrame.reindex_operator]
    exact frameResponseTransition_operator F _ (norm_firstDirection n) x p

/-- The action which is exposed: adjoint for a query, forward for a response. -/
noncomputable def ExposureKind.action (kind : ExposureKind) (A : E →L[ℝ] E) (x : E) : E :=
  match kind with
  | .query => A.adjoint x
  | .response => A x

/-- The revealed action is a function of the enlarged history alone. -/
noncomputable def ExposureFrame.exposedValue {n : ℕ} (F : ExposureFrame (Coordinates (n + 1)) E)
    (kind : ExposureKind) (x : E) (ξ : Coordinates (n + 1)) : E :=
  match kind with
  | .query => F.known.adjoint x + ‖F.physical.toContinuousLinearMap.adjoint x‖ • F.latent ξ
  | .response => F.known x + ‖F.latent.toContinuousLinearMap.adjoint x‖ • F.physical ξ

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem standardTransition_value {n : ℕ} (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (n + 1)) E) (x : Ω → E)
    (p : Ω × Rotation (Coordinates (n + 1))) :
    kind.action ((F p.1).operator p.2) (x p.1) =
      (F p.1).exposedValue kind (x p.1) (standardTransition kind F x p).1.2 := by
  cases kind with
  | query => exact (F p.1).query_vector _ (norm_firstDirection n) (x p.1) p.2
  | response => exact (F p.1).response_vector _ (norm_firstDirection n) (x p.1) p.2

theorem ExposureFrame.MeasurableFamily.exposedValue {n : ℕ}
    {F : Ω → ExposureFrame (Coordinates (n + 1)) E} (hF : ExposureFrame.MeasurableFamily F)
    (kind : ExposureKind) {x : Ω → E} (hx : Measurable x) :
    Measurable (fun p : Ω × Coordinates (n + 1) => (F p.1).exposedValue kind (x p.1) p.2) := by
  have hf : Measurable (Prod.fst : Ω × Coordinates (n + 1) → Ω) := measurable_fst
  have hK := hF.known.comp hf
  have hP := hF.physical.comp hf
  have hL := hF.latent.comp hf
  have hX := hx.comp hf
  cases kind with
  | query =>
    exact (measurable_operator_apply (measurable_operator_adjoint hK) hX).add
      ((measurable_operator_apply (measurable_operator_adjoint hP) hX).norm.smul
        (measurable_operator_apply hL measurable_snd))
  | response =>
    exact (measurable_operator_apply hK hX).add
      ((measurable_operator_apply (measurable_operator_adjoint hL) hX).norm.smul
        (measurable_operator_apply hP measurable_snd))

end RandomizedFO2003.Rotations
