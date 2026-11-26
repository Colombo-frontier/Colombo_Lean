import Smoothness2601.CoordinatePopulation
import Smoothness2601.InnerOracle

/-! Coordinate transport of the original full-gradient history kernel, with
unchanged centering, second moments, variance budget and hidden history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
namespace Smoothness2601.CoordinateOracle
open CoordinateGeometry

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {b : Budgets} (P : Population (X := X) (Y := Y) b) (e : Z ≃ₗᵢ[ℝ] Y)
  {H : Type} [MeasurableSpace H]

def query (q : Adaptive.Query X Z) : Adaptive.Query X Y := (q.1,(q.2.1,e q.2.2))

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [BorelSpace X] [SecondCountableTopology X] [SecondCountableTopology Y] [SecondCountableTopology Z] in
theorem query_measurable : Measurable (query (X := X) e) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (e.continuous.measurable.comp (measurable_snd.comp measurable_snd)))

def reply (z : Joint X Y × H) : Joint X Z × H := ((joint e).symm z.1,z.2)

omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology X] [SecondCountableTopology Y] [SecondCountableTopology Z] in
theorem reply_measurable : Measurable (reply (X := X) (H := H) e) :=
  ((joint e).symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
theorem trueGradient (q : Adaptive.Query X Z) :
    Adaptive.trueGradient (CoordinatePopulation.transport P e) q =
      (joint e).symm (Adaptive.trueGradient P (query e q)) := by
  rcases q with ⟨flag,x,y⟩
  cases flag <;> rfl

def law (O : Adaptive.Oracle P H) : Kernel (Adaptive.Query X Z × H) (Joint X Z × H) :=
  (O.law.comap (fun z => (query e z.1,z.2))
    (((query_measurable e).comp measurable_fst).prodMk measurable_snd)).map (reply e)

instance law_markov (O : Adaptive.Oracle P H) : IsMarkovKernel (law P e O) :=
  Kernel.IsMarkovKernel.map _ (reply_measurable e)

omit [CompleteSpace Z] [BorelSpace X] [SecondCountableTopology X] [SecondCountableTopology Y] [SecondCountableTopology Z] in
theorem law_apply (O : Adaptive.Oracle P H) (q : Adaptive.Query X Z) (h : H) :
    law P e O (q,h) = (O.law (query e q,h)).map (reply e) := by
  rw [law,Kernel.map_apply _ (reply_measurable e),Kernel.comap_apply]

def transport (O : Adaptive.Oracle P H) : Adaptive.Oracle (CoordinatePopulation.transport P e) H where
  law := law P e O
  markov := inferInstance
  square_integrable q h := by
    rw [law_apply]
    have hm : Measurable (fun z : Joint X Z × H =>
        ‖z.1-Adaptive.trueGradient (CoordinatePopulation.transport P e) q‖ ^ 2) :=
      (measurable_fst.sub measurable_const).norm.pow_const 2
    apply (integrable_map_measure hm.aestronglyMeasurable (reply_measurable e).aemeasurable).mpr
    change Integrable (fun z : Joint X Y × H =>
      ‖(joint e).symm z.1-Adaptive.trueGradient (CoordinatePopulation.transport P e) q‖ ^ 2)
      (O.law (query e q,h))
    simpa only [trueGradient,← map_sub,(joint e).symm.norm_map] using
      O.square_integrable (query e q) h
  centered q h := by
    rw [law_apply]
    have hm : Measurable (fun z : Joint X Z × H =>
        z.1-Adaptive.trueGradient (CoordinatePopulation.transport P e) q) :=
      measurable_fst.sub measurable_const
    rw [integral_map (reply_measurable e).aemeasurable hm.aestronglyMeasurable]
    simp only [reply,trueGradient,← map_sub]
    have hh := (joint (X := X) e).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := O.law (query e q,h)) (fun z : Joint X Y × H => z.1-Adaptive.trueGradient P (query e q))
    calc
      _ = (joint e).symm (∫ z, z.1-Adaptive.trueGradient P (query e q) ∂O.law (query e q,h)) := hh
      _ = 0 := by rw [O.centered,map_zero]
  variance q h := by
    rw [law_apply]
    have hm : Measurable (fun z : Joint X Z × H =>
        ‖z.1-Adaptive.trueGradient (CoordinatePopulation.transport P e) q‖ ^ 2) :=
      (measurable_fst.sub measurable_const).norm.pow_const 2
    rw [integral_map (reply_measurable e).aemeasurable hm.aestronglyMeasurable]
    simpa only [reply,trueGradient,← map_sub,(joint e).symm.norm_map] using
      O.variance (query e q) h

end Smoothness2601.CoordinateOracle
