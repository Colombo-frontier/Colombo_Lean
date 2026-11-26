import Nonsmooth.PosteriorMeanScaling
import Nonsmooth.PosteriorEnergyReencoding
import Nonsmooth.GaussianFirstQuery
import Nonsmooth.SupportCommonComponent

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)]

theorem supportSingleObservation_rows_scale (a : Fin k → E) (u : E) {c : ℝ} (hc : 0 < c) :
    supportSingleObservation u (scaleSupportRows c a) = (supportWinner a u, c * finiteSupport a u) := by
  have hw : supportWinner (scaleSupportRows c a) u = supportWinner a u := by
    apply (supportWinner_eq_iff _ _ _).mpr
    constructor
    · change finiteSupport (fun i => c • a i) u = ⟪c • a (supportWinner a u), u⟫_ℝ
      rw [finiteSupport_smul_rows a hc.le, real_inner_smul_left,
        supportWinner_attained a u]
    · intro j hj
      change ⟪c • a j, u⟫_ℝ < finiteSupport (fun i => c • a i) u
      rw [real_inner_smul_left, finiteSupport_smul_rows a hc.le]
      exact mul_lt_mul_of_pos_left
        (((supportWinner_eq_iff a u (supportWinner a u)).mp rfl).2 j hj) hc
  exact Prod.ext hw (finiteSupport_smul_rows a hc.le u)

theorem support_pulled_scale_energy (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : E) {c : ℝ} (hc : 0 < c) :
    (∫ h, ‖posteriorAggregateShift Q (supportSingleObservation u ∘ scaleSupportRows c) h‖ ^ 2
      ∂Q.map (supportSingleObservation u ∘ scaleSupportRows c)) =
    ∫ h, ‖posteriorAggregateShift Q (supportSingleObservation u) h‖ ^ 2
      ∂Q.map (supportSingleObservation u) := by
  let F : Fin k × ℝ → Fin k × ℝ := fun h => (h.1, c * h.2)
  let G : Fin k × ℝ → Fin k × ℝ := fun h => (h.1, c⁻¹ * h.2)
  apply posteriorAggregateEnergy_reencoding Q (supportSingleObservation u)
    (supportSingleObservation_measurable u) _
    ((supportSingleObservation_measurable u).comp (scaleSupportRows_measurable c))
    F (by fun_prop) G (by fun_prop)
  · intro a
    exact supportSingleObservation_rows_scale a u hc
  · intro a
    dsimp only [Function.comp_def]
    rw [supportSingleObservation_rows_scale a u hc]
    simp only [G, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    rfl

theorem support_aggregate_energy_scale (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : E) {c : ℝ} (hc : 0 < c) :
    letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
      Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
    (∫ h, ‖posteriorAggregateShift (Q.map (scaleSupportRows c)) (supportSingleObservation u) h‖ ^ 2
      ∂(Q.map (scaleSupportRows c)).map (supportSingleObservation u)) =
      c ^ 2 * ∫ h, ‖posteriorAggregateShift Q (supportSingleObservation u) h‖ ^ 2
        ∂Q.map (supportSingleObservation u) := by
  letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
    Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
  rw [posteriorAggregateEnergy_map_scale Q _ (supportSingleObservation_measurable u) c,
    support_pulled_scale_energy Q u hc]

end
end Nonsmooth
