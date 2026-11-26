import SampleReuse.CurvatureFirstTapes

open MeasureTheory
namespace SampleReuse
noncomputable section

/-- Splitting storage by derivative type does not change the law of the
one immutable iid sample tape used by the persistent oracle. -/
theorem derivativeTapes_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (G H : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun w : SampleTape G Ω × SampleTape H Ω => derivativeTapes w.1 w.2)
      ((sampleTapeLaw G μ).prod (sampleTapeLaw H μ)) (sampleTapeLaw (G+H) μ) := by
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin (G+H) => μ)
      (finSumFinEquiv : Fin G ⊕ Fin H ≃ Fin (G+H))).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin G ⊕ Fin H => μ))
  convert hp using 1
  funext w r
  refine Fin.addCases ?_ ?_ r
  · intro i
    simp only [derivativeTapes,Function.comp_def,Fin.addCases_left]
    rw [← finSumFinEquiv_apply_left i,MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  · intro i
    simp only [derivativeTapes,Function.comp_def,Fin.addCases_right]
    rw [← finSumFinEquiv_apply_right i,MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

theorem derivativeTapes_map {Ω : Type*} [MeasurableSpace Ω]
    (G H : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ((sampleTapeLaw G μ).prod (sampleTapeLaw H μ)).map
      (fun w => derivativeTapes w.1 w.2) = sampleTapeLaw (G+H) μ :=
  (derivativeTapes_measurePreserving G H μ).map_eq

/-- The same identification preserves an independent private-randomness
law, in particular the finite fair-sign law of the capped algorithm. -/
theorem derivativeTapes_signs_measurePreserving {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G H : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun w : (SampleTape G Ω × SampleTape H Ω) × Ξ =>
      (derivativeTapes w.1.1 w.1.2,w.2))
      (((sampleTapeLaw G μ).prod (sampleTapeLaw H μ)).prod ν)
      ((sampleTapeLaw (G+H) μ).prod ν) :=
  (derivativeTapes_measurePreserving G H μ).prod (MeasurePreserving.id ν)

end
end SampleReuse
