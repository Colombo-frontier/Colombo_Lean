import Nonsmooth.GaussianPolytopeActualEnergy
import Nonsmooth.ParametricSupportEnergy
import Nonsmooth.RecursiveGaussianConsequences

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {r : ℕ}

theorem gaussianPolytope_independent_actual_log_energy {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hi : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i))) (q : E) :
    (∫ y, ‖posteriorAggregateShift Q (supportSingleObservation q) y‖ ^ 2
      ∂Q.map (supportSingleObservation q)) ≤
        512 * s ^ 2 * Real.log (Real.exp 1 * ((r + 1 : ℕ) : ℝ)) := by
  let μ (i : Fin (r + 1)) := Q.map (fun a => a i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hprod : Q = Measure.pi μ := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin (r + 1) => (measurable_pi_apply i).aemeasurable)).mp hi
    change Q.map id = Measure.pi μ at h
    simpa only [Measure.map_id] using h
  have h := gaussianPolytopeRows_actual_log_energy hs μ hrow q
  simpa only [← hprod] using h

theorem gaussianPolytope_parametric_energy_at {α : Type} [MeasurableSpace α]
    {s : ℝ} (hs : 0 < s) (κ : Kernel α (Fin (r + 1) → E)) [IsMarkovKernel κ]
    (u : α → E) (hu : Measurable u) (x : α)
    (hi : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) (κ x))
    (hrow : ∀ i, GaussianPolytopeRow s ((κ x).map (fun a => a i))) :
    supportUpdateMeanEnergy κ u hu x ≤
      512 * s ^ 2 * Real.log (Real.exp 1 * ((r + 1 : ℕ) : ℝ)) := by
  rw [supportUpdateMeanEnergy_eq_actual]
  exact gaussianPolytope_independent_actual_log_energy hs (κ x) hi hrow (u x)

theorem recursiveGaussian_step_energy_ae {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    ∀ᵐ h ∂Q.map (recursiveSupportResponse u n),
      supportUpdateMeanEnergy (recursiveSupportBelief Q u hu n) (u n) (hu n) h ≤
        512 * s ^ 2 * Real.log (Real.exp 1 * ((r + 1 : ℕ) : ℝ)) := by
  apply recursiveGaussian_measurable_consequence hs Q hQ hrow u hu n
    (fun h => supportUpdateMeanEnergy (recursiveSupportBelief Q u hu n) (u n) (hu n) h ≤ _)
    (measurableSet_le (supportUpdateMeanEnergy_measurable _ _ _) measurable_const)
  intro h hh
  exact gaussianPolytope_parametric_energy_at hs _ _ _ h hh.1 hh.2

end
end Nonsmooth
