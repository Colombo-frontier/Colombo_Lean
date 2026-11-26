import Bilevel.TransportControllerStore
import Bilevel.TransportNetworkQueryMoment
import Bilevel.TransportNetworkObservation

/-! Arbitrary raw query vectors, including the zero-residual branch. The
measurable projector store computes the normalized residual only for the
energy analysis; the actual observation is still the original raw query. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportControllerQuery
open EuclideanGaussian ProjectionGeometry TransportObserver TransportNetwork
set_option maxHeartbeats 500000

theorem raw_energy_increment (D : ℕ) (V : Submodule ℝ (Space D))
    {κ : Type*} (U : κ → Space D) (I : Finset κ) (q : Space D) :
    frameEnergy (V ⊔ Submodule.span ℝ {q}) U I-frameEnergy V U I =
      ∑ i ∈ I, ⟪revelationDirection V q,U i⟫^2 := by
  by_cases hz : ProjectionGeometry.residual V q = 0
  · rw [ProjectionNormalization.unchanged D V q hz]
    simp [revelationDirection,hz]
  · rw [ProjectionNormalization.span_eq D V q hz]
    exact query_energy_increment V U I _ (ProjectionNormalization.direction_mem D V q)
      (ProjectionNormalization.direction_norm D V q hz)

theorem raw_increment_measurable (D m T : ℕ) :
    Measurable (fun p : (Fin m → Space D) × Space D × (Fin T → Space D) =>
      frameEnergy (TransportGeneratorStore.span p.1 ⊔ Submodule.span ℝ {p.2.1}) p.2.2 Finset.univ-
        frameEnergy (TransportGeneratorStore.span p.1) p.2.2 Finset.univ) := by
  simp_rw [raw_energy_increment]
  have hd : Measurable (fun p : (Fin m → Space D) × Space D × (Fin T → Space D) =>
      revelationDirection (TransportGeneratorStore.span p.1) p.2.1) := by
    have hh := ProjectionStore.direction_measurable
      (Ω := (Fin m → Space D) × Space D × (Fin T → Space D)) D _
      ((TransportGeneratorStore.projector_measurable D m).comp measurable_fst) _
      (measurable_fst.comp measurable_snd)
    simpa only [Function.comp_apply,TransportGeneratorStore.projector_correct,ProjectionStore.direction_subspace] using hh
  apply Finset.measurable_sum
  intro i _
  have hu : Measurable (fun p : (Fin m → Space D) × Space D × (Fin T → Space D) => p.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact ((continuous_fst.inner continuous_snd).measurable.comp (hd.prodMk hu)).pow_const 2

theorem raw_query_failure {n D : ℕ} (T : ℕ) (hT : T ≤ D)
    (W : Known n D) (μ : Measure (Latent n D)) [IsProbabilityMeasure μ]
    (hμ : Invariant W μ) (v : Vertex n) (d : ℕ)
    (hW : Module.finrank ℝ (W v) ≤ d) (hd : d < D)
    (q : Space D) (a : ℝ) (ha : 0 < a) :
    μ.real {z | a < frameEnergy (W v ⊔ Submodule.span ℝ {q}) (frame T hT z v) Finset.univ-
      frameEnergy (W v) (frame T hT z v) Finset.univ} ≤ (T:ℝ)/(((D:ℝ)-d)*a) := by
  by_cases hz : ProjectionGeometry.residual (W v) q = 0
  · rw [ProjectionNormalization.unchanged D (W v) q hz]
    have hn : (0:ℝ) ≤ (D:ℝ)-d := by
      have hh : (d:ℝ) < D := by exact_mod_cast hd
      linarith
    simp only [sub_self,not_lt_of_ge ha.le,Set.setOf_false,measureReal_empty]
    exact div_nonneg (Nat.cast_nonneg T) (mul_nonneg hn ha.le)
  · simp_rw [raw_energy_increment]
    exact query_failure_dimension T hT W μ hμ v d hW hd _
      (ProjectionNormalization.direction_mem D (W v) q)
      (ProjectionNormalization.direction_norm D (W v) q hz) a ha

/-- Observation and energy control concern the same arbitrary raw query;
normalization is not an extra assumption on the algorithm. -/
theorem raw_query_step {n D : ℕ} (T : ℕ) (hT : T ≤ D)
    (W : Known n D) (μ : Measure (Latent n D)) [IsProbabilityMeasure μ]
    (hμ : Invariant W μ) (v : Vertex n) (d : ℕ)
    (hW : Module.finrank ℝ (W v) ≤ d) (hd : d < D) (q : Space D) (a : ℝ) (ha : 0 < a) :
    (∀ᵐ y ∂μ.map (queryObservation T hT v q),
      Invariant (insert W v q) (condDistrib id (queryObservation T hT v q) μ y)) ∧
    μ.real {z | a < frameEnergy (W v ⊔ Submodule.span ℝ {q}) (frame T hT z v) Finset.univ-
      frameEnergy (W v) (frame T hT z v) Finset.univ} ≤ (T:ℝ)/(((D:ℝ)-d)*a) :=
  ⟨query_posterior_invariant T hT W μ hμ v q,
    raw_query_failure T hT W μ hμ v d hW hd q a ha⟩

end Bilevel.TransportControllerQuery
