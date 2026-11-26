import RandomizedFO2003.FrameStep
import RandomizedFO2003.FrameMeasurability

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {Ω E S : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S]

theorem ExposureFrame.MeasurableFamily.queryDirection {F : Ω → ExposureFrame S E}
    (hF : ExposureFrame.MeasurableFamily F) (e : S) {x : Ω → E} (hx : Measurable x) :
    Measurable (fun ω => (F ω).queryDirection e (x ω)) :=
  (measurable_unitQueryDirection e).comp
    (measurable_operator_apply (measurable_operator_adjoint hF.physical) hx)

theorem ExposureFrame.MeasurableFamily.responseDirection {F : Ω → ExposureFrame S E}
    (hF : ExposureFrame.MeasurableFamily F) (e : S) {y : Ω → E} (hy : Measurable y) :
    Measurable (fun ω => (F ω).responseDirection e (y ω)) :=
  (measurable_unitQueryDirection e).comp
    (measurable_operator_apply (measurable_operator_adjoint hF.latent) hy)

theorem ExposureFrame.MeasurableFamily.afterQuery {F : Ω → ExposureFrame S E}
    (hF : ExposureFrame.MeasurableFamily F) (e : S) {x : Ω → E} (hx : Measurable x) :
    ExposureFrame.MeasurableFamily (fun p : Ω × S => (F p.1).afterQuery e (x p.1) p.2) :=
  (hF.comp measurable_fst).refine e
    ((measurable_section e).comp ((hF.queryDirection e hx).comp measurable_fst))
    ((measurable_section e).comp measurable_snd)

theorem ExposureFrame.MeasurableFamily.afterResponse {F : Ω → ExposureFrame S E}
    (hF : ExposureFrame.MeasurableFamily F) (e : S) {y : Ω → E} (hy : Measurable y) :
    ExposureFrame.MeasurableFamily (fun p : Ω × S => (F p.1).afterResponse e (y p.1) p.2) :=
  (hF.comp measurable_fst).refine e
    ((measurable_section e).comp measurable_snd)
    ((measurable_section e).comp ((hF.responseDirection e hy).comp measurable_fst))

noncomputable def frameQueryTransition (F : Ω → ExposureFrame S E) (e : S) (x : Ω → E)
    (p : Ω × Rotation S) : (Ω × S) × Rotation (Submodule.span ℝ {e})ᗮ :=
  let q := (F p.1).querySplit e (x p.1) p.2
  ((p.1, q.1), q.2⁻¹)

noncomputable def frameResponseTransition (F : Ω → ExposureFrame S E) (e : S) (y : Ω → E)
    (p : Ω × Rotation S) : (Ω × S) × Rotation (Submodule.span ℝ {e})ᗮ :=
  let q := (F p.1).responseSplit e (y p.1) p.2
  ((p.1, q.1), q.2)

/-- One inverse exposure updates both frames using only the enlarged history;
the smaller residual rotation has independent Haar law. -/
theorem frameQueryTransition_preserving (μ : Measure Ω) [SFinite μ]
    (F : Ω → ExposureFrame S E) (hF : ExposureFrame.MeasurableFamily F)
    (e : S) (he : ‖e‖ = 1) (x : Ω → E) (hx : Measurable x) :
    MeasurePreserving (frameQueryTransition F e x) (μ.prod (haarLaw S))
      ((μ.prod (Spherical.sphereLaw S)).prod (haarLaw (Submodule.span ℝ {e})ᗮ)) := by
  have hp := queryCoordinates_preserving μ e he (fun ω => (F ω).queryDirection e (x ω))
    (hF.queryDirection e hx)
  have hi := (MeasurePreserving.id μ).prod
    ((MeasurePreserving.id (Spherical.sphereLaw S)).prod (haar_inverse (Submodule.span ℝ {e})ᗮ))
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ
    (Spherical.sphereLaw S) (haarLaw (Submodule.span ℝ {e})ᗮ))).comp (hi.comp hp)

theorem frameResponseTransition_preserving (μ : Measure Ω) [SFinite μ]
    (F : Ω → ExposureFrame S E) (hF : ExposureFrame.MeasurableFamily F)
    (e : S) (he : ‖e‖ = 1) (y : Ω → E) (hy : Measurable y) :
    MeasurePreserving (frameResponseTransition F e y) (μ.prod (haarLaw S))
      ((μ.prod (Spherical.sphereLaw S)).prod (haarLaw (Submodule.span ℝ {e})ᗮ)) :=
  (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ
    (Spherical.sphereLaw S) (haarLaw (Submodule.span ℝ {e})ᗮ))).comp
      (responseCoordinates_preserving μ e he (fun ω => (F ω).responseDirection e (y ω))
        (hF.responseDirection e hy))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Ω] in
theorem frameQueryTransition_operator (F : Ω → ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (x : Ω → E) (p : Ω × Rotation S) :
    (F p.1).operator p.2 =
      ((F (frameQueryTransition F e x p).1.1).afterQuery e
        (x (frameQueryTransition F e x p).1.1) (frameQueryTransition F e x p).1.2).operator
          (frameQueryTransition F e x p).2 :=
  (F p.1).queryStep_operator e he (x p.1) p.2

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Ω] in
theorem frameResponseTransition_operator (F : Ω → ExposureFrame S E)
    (e : S) (he : ‖e‖ = 1) (y : Ω → E) (p : Ω × Rotation S) :
    (F p.1).operator p.2 =
      ((F (frameResponseTransition F e y p).1.1).afterResponse e
        (y (frameResponseTransition F e y p).1.1) (frameResponseTransition F e y p).1.2).operator
          (frameResponseTransition F e y p).2 :=
  (F p.1).responseStep_operator e he (y p.1) p.2

end RandomizedFO2003.Rotations
