import SecondOrder.IndependentDraws
import SecondOrder.BranchedOjaProgram

open MeasureTheory

namespace SecondOrder
noncomputable section

abbrev OjaTrialSamples (Ω : Type) (d : ℕ) (P : Parameters) (γ δ : ℝ) :=
  Draws Ω (ojaIterationCount d (ojaCurvatureTolerance P γ)) ×
    LocalDraws Ω (P.hessianBound^2) (γ/8) δ

def ojaTrialSamplesLaw {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Parameters) (d : ℕ) (γ δ : ℝ) : Measure (OjaTrialSamples Ω d P γ δ) :=
  (drawsLaw μ (ojaIterationCount d (ojaCurvatureTolerance P γ))).prod
    (localLaw μ (P.hessianBound^2) (γ/8) δ)

instance ojaTrialSamplesLaw_probability {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (d : ℕ) (γ δ : ℝ) :
    IsProbabilityMeasure (ojaTrialSamplesLaw μ P d γ δ) := by
  unfold ojaTrialSamplesLaw
  infer_instance

def ojaTrialSplit {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaTrialDraws Ω d P γ δ) : OjaTrialSeed d P γ × OjaTrialSamples Ω d P γ δ :=
  ((w.1.1.2,w.1.2),(w.1.1.1,w.2))

theorem ojaTrialSplit_measurePreserving {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) {d : ℕ} (hd : 0<d)
    {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    MeasurePreserving (ojaTrialSplit (Ω := Ω) P γ δ) (ojaTrialLaw μ P hd hγ δ)
      ((ojaTrialSeedLaw P hd hγ).prod (ojaTrialSamplesLaw μ P d γ δ)) := by
  letI : NeZero (ojaIterationCount d (ojaCurvatureTolerance P γ)) :=
    ⟨(ojaIterationCount_pos hd (ojaCurvatureTolerance_pos P hγ)).ne'⟩
  exact product_rotate_seed (drawsLaw μ (ojaIterationCount d (ojaCurvatureTolerance P γ)))
    (signLaw d) (PMF.uniformOfFintype _).toMeasure (localLaw μ (P.hessianBound^2) (γ/8) δ)

def ojaAmplifiedSplit {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaAmplifiedDraws Ω d P γ δ) :
    OjaAmplifiedSeed d P γ δ × Draws (OjaTrialSamples Ω d P γ (ojaValidationFailure δ)) (ojaRepeats δ) :=
  let u := drawsUnzip (ojaRepeats δ)
    (drawsMap (ojaTrialSplit P γ (ojaValidationFailure δ)) (ojaRepeats δ) w)
  (drawsVector id (ojaRepeats δ) u.1,u.2)

/-- All initialization signs and candidate indices are independent of all
generation and validation samples, including after amplification. -/
theorem ojaAmplifiedSplit_measurePreserving {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) {d : ℕ} (hd : 0<d)
    {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    MeasurePreserving (ojaAmplifiedSplit (Ω := Ω) P γ δ) (ojaAmplifiedLaw μ P hd hγ δ)
      ((ojaAmplifiedSeedLaw P hd hγ δ).prod
        (drawsLaw (ojaTrialSamplesLaw μ P d γ (ojaValidationFailure δ)) (ojaRepeats δ))) := by
  have hs := ojaTrialSplit_measurePreserving μ P hd hγ (ojaValidationFailure δ)
  have hm := drawsMap_measurePreserving hs (ojaRepeats δ)
  have hu := drawsUnzip_measurePreserving (ojaTrialSeedLaw P hd hγ)
    (ojaTrialSamplesLaw μ P d γ (ojaValidationFailure δ)) (ojaRepeats δ)
  have hv : MeasurePreserving (drawsVector id (ojaRepeats δ))
      (drawsLaw (ojaTrialSeedLaw P hd hγ) (ojaRepeats δ)) (ojaAmplifiedSeedLaw P hd hγ δ) :=
    ⟨drawsVector_measurable measurable_id _,rfl⟩
  exact (hv.prod (MeasurePreserving.id _)).comp (hu.comp hm)

theorem ojaAmplifiedSplit_seed {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaAmplifiedDraws Ω d P γ δ) (i : Fin (ojaRepeats δ)) :
    (ojaAmplifiedSplit P γ δ w).1 i=
      ((drawsVector id (ojaRepeats δ) w i).1.1.2,(drawsVector id (ojaRepeats δ) w i).1.2) := by
  change drawsVector id _ (drawsUnzip _ (drawsMap _ _ w)).1 i=_
  rw [drawsVector_unzip_fst,drawsVector_drawsMap]
  rfl

end
end SecondOrder
