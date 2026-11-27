import Nonsmooth.PosteriorAggregateEnergy
import Nonsmooth.ConditionalReencoding

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E H G : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace H] [MeasurableSpace G] {k : ℕ}

theorem posteriorAggregateShift_measurable (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) : Measurable (posteriorAggregateShift Q X) := by
  have hf : StronglyMeasurable (fun a : Fin k → E => ∑ i, a i) :=
    (continuous_finsetSum _ (fun i _ => continuous_apply i)).stronglyMeasurable
  exact (hf.integral_kernel.sub stronglyMeasurable_const).measurable

theorem posteriorAggregateEnergy_reencoding (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X)
    (Z : (Fin k → E) → G) (hZ : Measurable Z)
    (f : H → G) (hf : Measurable f) (g : G → H) (hg : Measurable g)
    (hZX : ∀ a, Z a = f (X a)) (hXZ : ∀ a, g (Z a) = X a) :
    (∫ z, ‖posteriorAggregateShift Q Z z‖ ^ 2 ∂Q.map Z) =
      ∫ x, ‖posteriorAggregateShift Q X x‖ ^ 2 ∂Q.map X := by
  have hp := condDistrib_reencoding Q X hX id measurable_id Z hZ f hf g hg hZX hXZ
  have hmap : (Q.map Z).map g = Q.map X := by
    rw [Measure.map_map hg hZ]
    congr 1
    funext a
    exact hXZ a
  have hm : StronglyMeasurable (fun x => ‖posteriorAggregateShift Q X x‖ ^ 2) :=
    ((posteriorAggregateShift_measurable Q X).norm.pow_const 2).stronglyMeasurable
  calc
    _ = ∫ z, ‖posteriorAggregateShift Q X (g z)‖ ^ 2 ∂Q.map Z := by
      apply integral_congr_ae
      filter_upwards [hp] with z hz
      simp only [posteriorAggregateShift, hz]
    _ = ∫ x, ‖posteriorAggregateShift Q X x‖ ^ 2 ∂(Q.map Z).map g :=
      (integral_map_of_stronglyMeasurable hg hm).symm
    _ = _ := by rw [hmap]

end
end Nonsmooth
