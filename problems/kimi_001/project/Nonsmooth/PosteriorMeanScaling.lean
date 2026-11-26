import Nonsmooth.PosteriorAggregateEnergy
import Nonsmooth.ConditionalImage

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace H] {k : ℕ}

def scaleSupportRows (c : ℝ) (a : Fin k → E) : Fin k → E := fun i => c • a i

theorem scaleSupportRows_measurable (c : ℝ) : Measurable (scaleSupportRows (E := E) (k := k) c) :=
  measurable_pi_lambda _ (fun i => measurable_const.smul (measurable_pi_apply i))

theorem posteriorAggregateShift_map_scale (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X) (c : ℝ) :
    letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
      Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
    ∀ᵐ h ∂(Q.map (scaleSupportRows c)).map X,
      posteriorAggregateShift (Q.map (scaleSupportRows c)) X h =
        c • posteriorAggregateShift Q (X ∘ scaleSupportRows c) h := by
  letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
    Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
  have hsum : StronglyMeasurable (fun a : Fin k → E => ∑ i, a i) := by
    exact (continuous_finsetSum _ (fun i _ => continuous_apply i)).stronglyMeasurable
  have hint (ν : Measure (Fin k → E)) :
      (∫ a : Fin k → E, ∑ i, a i ∂ν.map (scaleSupportRows c)) =
        c • ∫ a : Fin k → E, ∑ i, a i ∂ν := by
    rw [integral_map_of_stronglyMeasurable (scaleSupportRows_measurable c) hsum]
    simp only [scaleSupportRows, ← Finset.smul_sum, integral_smul]
  filter_upwards [condDistrib_map_prior Q (scaleSupportRows c) (scaleSupportRows_measurable c) X hX]
    with h hh
  simp only [posteriorAggregateShift, hh, hint, smul_sub]

theorem posteriorAggregateEnergy_map_scale (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (X : (Fin k → E) → H) (hX : Measurable X) (c : ℝ) :
    letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
      Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
    (∫ h, ‖posteriorAggregateShift (Q.map (scaleSupportRows c)) X h‖ ^ 2
      ∂(Q.map (scaleSupportRows c)).map X) =
      c ^ 2 * ∫ h, ‖posteriorAggregateShift Q (X ∘ scaleSupportRows c) h‖ ^ 2
        ∂Q.map (X ∘ scaleSupportRows c) := by
  letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
    Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
  calc
    _ = ∫ h, c ^ 2 * ‖posteriorAggregateShift Q (X ∘ scaleSupportRows c) h‖ ^ 2
        ∂(Q.map (scaleSupportRows c)).map X := by
      apply integral_congr_ae
      filter_upwards [posteriorAggregateShift_map_scale Q X hX c] with h hh
      rw [hh, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ = _ := by rw [integral_const_mul, Measure.map_map hX (scaleSupportRows_measurable c)]

end
end Nonsmooth
