import Nonsmooth.ProductMarginals

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

theorem supportParametricObservation_measurable {k : ℕ} [Nonempty (Fin k)]
    (u : α → E) (hu : Measurable u) :
    Measurable (fun p : α × (Fin k → E) => supportSingleObservation (u p.1) p.2) := by
  have hp : Measurable (fun p : α × (Fin k → E) => (p.2, u p.1)) :=
    measurable_snd.prodMk (hu.comp measurable_fst)
  exact ((supportWinner_measurable (E := E) (k := k)).comp hp).prodMk
    ((finiteSupport_joint_continuous (E := E) (ι := Fin k)).measurable.comp hp)

def supportPosteriorUpdate {k : ℕ} [Nonempty (Fin k)]
    (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ] (u : α → E) (hu : Measurable u) :
    Kernel (α × (Fin k × ℝ)) (Fin k → E) :=
  observedPosterior κ (fun p => supportSingleObservation (u p.1) p.2)
    (supportParametricObservation_measurable u hu)

instance supportPosteriorUpdate_markov {k : ℕ} [Nonempty (Fin k)]
    (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ] (u : α → E) (hu : Measurable u) :
    IsMarkovKernel (supportPosteriorUpdate κ u hu) := by
  unfold supportPosteriorUpdate
  infer_instance

/-- At each fixed history, an independent row law remains independent after the next adaptive query. -/
theorem supportPosteriorUpdate_independent_at
    (κ : Kernel α (Fin (n + 1) → E)) [IsMarkovKernel κ] (u : α → E) (hu : Measurable u)
    (x : α) (hx : iIndepFun (fun i (a : Fin (n + 1) → E) => a i) (κ x)) :
    ∀ᵐ y ∂(κ x).map (supportSingleObservation (u x)),
      iIndepFun (fun i (a : Fin (n + 1) → E) => a i) (supportPosteriorUpdate κ u hu (x, y)) := by
  let μ (i : Fin (n + 1)) : Measure E := (κ x).map (fun a => a i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i => Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hprod : κ x = Measure.pi μ := by
    have h := (independent_iff_productMarginalKernel κ x).mp hx
    rwa [productMarginalKernel_apply] at h
  have hp := observedPosterior_ae_eq_condDistrib κ
    (fun p : α × (Fin (n + 1) → E) => supportSingleObservation (u p.1) p.2)
    (supportParametricObservation_measurable u hu) x
  change ∀ᵐ y ∂(κ x).map (supportSingleObservation (u x)),
    supportPosteriorUpdate κ u hu (x, y) = condDistrib id (supportSingleObservation (u x)) (κ x) y at hp
  simp only [hprod] at hp ⊢
  filter_upwards [hp, supportSingleObservation_posterior_independent μ (u x)] with y hy hi
  rw [hy]
  exact hi

/-- Independence is preserved under mixing histories, with the actual conditional response law. -/
theorem supportPosteriorUpdate_independent
    (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α (Fin (n + 1) → E)) [IsMarkovKernel κ] (u : α → E) (hu : Measurable u)
    (h : ∀ᵐ x ∂ν, iIndepFun (fun i (a : Fin (n + 1) → E) => a i) (κ x)) :
    ∀ᵐ p ∂ν ⊗ₘ (observedKernel κ
      (fun p => supportSingleObservation (u p.1) p.2)
      (supportParametricObservation_measurable u hu)).fst,
      iIndepFun (fun i (a : Fin (n + 1) → E) => a i) (supportPosteriorUpdate κ u hu p) := by
  let η := supportPosteriorUpdate κ u hu
  let ξ := observedKernel κ (fun p => supportSingleObservation (u p.1) p.2)
    (supportParametricObservation_measurable u hu)
  have he : η =ᵐ[ν ⊗ₘ ξ.fst] productMarginalKernel η := by
    apply kernel_ae_eq_of_ae_ae ν ξ.fst η (productMarginalKernel η)
    filter_upwards [h] with x hx
    rw [observedKernel_fst]
    filter_upwards [supportPosteriorUpdate_independent_at κ u hu x hx] with y hy
    exact (independent_iff_productMarginalKernel η (x, y)).mp hy
  filter_upwards [he] with p hp
  rw [hp]
  exact productMarginalKernel_independent η p

end
end Nonsmooth
