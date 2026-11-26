import Nonsmooth.RecursiveGaussianConsequences
import Nonsmooth.GaussianPolytopeMoments
import Nonsmooth.ConditionalRowCovarianceDense

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {r : ℕ}

/-- A static covariance bound for the geometric row class implies the actual
finite-horizon adaptive posterior bound, with one exceptional set for all directions. -/
theorem recursiveGaussian_covariance_of_row_bound {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (u : ∀ n, ResponseHistory (r + 1) n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (C : ℝ)
    (hcov : ∀ (ν : Measure E) [IsProbabilityMeasure ν], GaussianPolytopeRow s ν →
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤ C * ‖v‖ ^ 2) :
    ∀ᵐ h ∂Q.map (recursiveSupportResponse u n), ∀ (v : E) (i : Fin (r + 1)),
      variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ)
        (condDistrib id (recursiveSupportResponse u n) Q h) ≤ C * ‖v‖ ^ 2 := by
  have hL : ∀ i, MemLp (fun a : Fin (r + 1) → E => a i) 2 Q := by
    intro i
    let ν := Q.map (fun a => a i)
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).mp (gaussianPolytopeRow_memLp s ν (hrow i))
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense E
  apply conditional_covariance_from_dense Q _ (recursiveSupportResponse_measurable u hu n) hL D hdense C
  let K := recursiveSupportBelief Q u hu n
  let P : ResponseHistory (r + 1) n → Measure (Fin (r + 1) → E) → Prop :=
    fun _ ν => ∀ v ∈ D, ∀ i, variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ) ν ≤ C * ‖v‖ ^ 2
  have hm : MeasurableSet {h | P h (K h)} := by
    have he : {h | P h (K h)} = ⋂ v ∈ D, ⋂ i : Fin (r + 1),
        {h | variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ) (K h) ≤ C * ‖v‖ ^ 2} := by
      ext h
      simp only [P, mem_setOf_eq, mem_iInter]
    rw [he]
    apply MeasurableSet.biInter hD
    intro v hv
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (kernel_variance_measurable K _ (by fun_prop)) measurable_const
  apply recursiveGaussian_actual_posterior_consequence hs Q hQ hrow u hu n P hm
  intro h hh v hv i
  let ν := (K h).map (fun a => a i)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hb := hcov ν (hh.2 i) v
  have he := variance_map_measurable (K h) (fun a => a i) (measurable_pi_apply i)
    (fun z : E => ⟪v, z⟫_ℝ) (by fun_prop)
  exact he.symm.trans_le hb

end
end Nonsmooth
