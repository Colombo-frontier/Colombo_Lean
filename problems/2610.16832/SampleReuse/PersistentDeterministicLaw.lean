import SampleReuse.PersistentDeterministicBridge
import SampleReuse.PersistentInfiniteTape

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section
variable {d : ℕ} {H S Ξ : Type} [MeasurableSpace S] [MeasurableSpace Ξ]

theorem deterministicBridge_success_probability
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) (f : Point d → ℝ) (success : Point d → Prop)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] :
    (μ.prod (iidSampleTapeLaw (PMF.pure ()))).real {w : Ξ × (ℕ → Unit) |
      (P w.1).Halts (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2 ∧
      success ((P w.1).outputFor (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2)} =
    μ.real {ξ | (deterministicFullJetPolicy P hP).Halts f ξ ∧
      success ((deterministicFullJetPolicy P hP).outputFor f ξ)} := by
  haveI : IsProbabilityMeasure (iidSampleTapeLaw (PMF.pure () : PMF Unit)) := iidSampleTapeLaw_probability _
  haveI : IsFiniteMeasure (iidSampleTapeLaw (PMF.pure () : PMF Unit)) :=
    ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
  haveI : SigmaFinite (iidSampleTapeLaw (PMF.pure () : PMF Unit)) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (iidSampleTapeLaw (PMF.pure () : PMF Unit)) := inferInstance
  have he : {w : Ξ × (ℕ → Unit) |
      (P w.1).Halts (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2 ∧
      success ((P w.1).outputFor (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2)} =
      {ξ | (deterministicFullJetPolicy P hP).Halts f ξ ∧
        success ((deterministicFullJetPolicy P hP).outputFor f ξ)} ×ˢ Set.univ := by
    ext w
    simp only [Set.mem_setOf_eq,Set.mem_prod,Set.mem_univ,and_true]
    rw [deterministicBridge_halts P hP f w.1 w.2,deterministicBridge_output P hP f w.1 w.2]
  rw [he,measureReal_prod_prod (μ := μ) (ν := iidSampleTapeLaw (PMF.pure () : PMF Unit))]
  simp only [measureReal_univ_eq_one,mul_one]

theorem deterministicBridge_expected
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (hP : MeasurableStoppingFamily P) {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] :
    (∫⁻ w : Ξ × (ℕ → Unit),
      (P w.1).extendedCost (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2
      ∂μ.prod (iidSampleTapeLaw (PMF.pure ()))) =
    ∫⁻ ξ, (deterministicFullJetPolicy P hP).extendedCost f ξ ∂μ := by
  haveI : IsProbabilityMeasure (iidSampleTapeLaw (PMF.pure () : PMF Unit)) := iidSampleTapeLaw_probability _
  haveI : IsFiniteMeasure (iidSampleTapeLaw (PMF.pure () : PMF Unit)) :=
    ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
  haveI : SigmaFinite (iidSampleTapeLaw (PMF.pure () : PMF Unit)) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (iidSampleTapeLaw (PMF.pure () : PMF Unit)) := inferInstance
  have he : (fun w : Ξ × (ℕ → Unit) =>
      (P w.1).extendedCost (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2) =
      fun w => (deterministicFullJetPolicy P hP).extendedCost f w.1 := by
    funext w
    exact (deterministicBridge_extendedCost P hP f w.1 w.2).symm
  rw [he]
  have hm : Measurable (fun w : Ξ × (ℕ → Unit) =>
      (deterministicFullJetPolicy P hP).extendedCost f w.1) :=
    ((deterministicFullJetPolicy P hP).measurable_extendedCost hf).comp measurable_fst
  rw [lintegral_prod (μ := μ) (ν := iidSampleTapeLaw (PMF.pure () : PMF Unit)) _ hm.aemeasurable]
  simp only [lintegral_const,measure_univ,mul_one]

end
end SampleReuse
