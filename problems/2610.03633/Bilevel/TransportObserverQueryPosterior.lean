import Bilevel.TransportObserverQueryMoment

/-! The fresh-query moment holds for the actual regular conditional laws
after a projection query or a named-column revelation. These are the genuine
posterior kernels, rather than laws postulated to satisfy a moment bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open EuclideanGaussian ProjectionGeometry
set_option synthInstance.maxHeartbeats 100000

theorem frame_norm_set_measurable (d T : ℕ) :
    MeasurableSet {U : ProjectionPosterior.Frame d T | ∀ i, ‖U i‖ ≤ 1} := by
  have he : {U : ProjectionPosterior.Frame d T | ∀ i, ‖U i‖ ≤ 1} =
      ⋂ i : Fin T, {U | ‖U i‖ ≤ 1} := by ext U; simp
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    (measurable_pi_apply i).norm measurable_const)

theorem query_posterior_total_moment {ι : Type*} [Fintype ι]
    (d T : ℕ) (V : Submodule ℝ (Space d))
    (μ : Measure (ProjectionPosterior.Frame d T)) [IsProbabilityMeasure μ]
    (hμ : ProjectionPosterior.Invariant d T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1) (q₀ : Space d)
    (b : OrthonormalBasis ι ℝ (V ⊔ Submodule.span ℝ {q₀})ᗮ)
    (hd : 0 < Fintype.card ι) :
    ∀ᵐ y ∂μ.map (ProjectionPosterior.queryObservation d T q₀),
      ∀ q : Space d, q ∈ (V ⊔ Submodule.span ℝ {q₀})ᗮ → ‖q‖ = 1 →
        (∫ U, ∑ i, ⟪q,U i⟫^2
          ∂condDistrib id (ProjectionPosterior.queryObservation d T q₀) μ y) ≤
          (T:ℝ)/(Fintype.card ι : ℝ) := by
  have hp := ProjectionPosterior.query_posterior_invariant d T V μ hμ q₀
  have hs := ConditionalSupport.support μ (ProjectionPosterior.queryObservation d T q₀)
    (ProjectionPosterior.query_measurable d T q₀) _ (frame_norm_set_measurable d T) hnorm
  filter_upwards [hp,hs] with y hy hyNorm
  intro q hqV hq
  exact invariant_query_total_moment d T (V ⊔ Submodule.span ℝ {q₀}) b hd _ hy hyNorm q hqV hq

/-- A named column may change the residual dimension and subspace. The
posterior invariance and its norm support still give the fresh-query moment
for every orthonormal coordinate choice in that actual residual subspace. -/
theorem reveal_posterior_total_moment (d T : ℕ) (V : Submodule ℝ (Space d))
    (μ : Measure (ProjectionPosterior.Frame d T)) [IsProbabilityMeasure μ]
    (hμ : ProjectionPosterior.Invariant d T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1) (i : Fin T)
    (r : Space d → ℕ)
    (b : ∀ y : Space d, OrthonormalBasis (Fin (r y)) ℝ (V ⊔ Submodule.span ℝ {y})ᗮ) :
    ∀ᵐ y ∂μ.map (ProjectionPosterior.revealObservation d T i),
      0 < r y → ∀ q : Space d, q ∈ (V ⊔ Submodule.span ℝ {y})ᗮ → ‖q‖ = 1 →
        (∫ U, ∑ j, ⟪q,U j⟫^2
          ∂condDistrib id (ProjectionPosterior.revealObservation d T i) μ y) ≤
          (T:ℝ)/(r y:ℝ) := by
  have hp := ProjectionPosterior.reveal_posterior_invariant d T V μ hμ i
  have hs := ConditionalSupport.support μ (ProjectionPosterior.revealObservation d T i)
    (ProjectionPosterior.reveal_measurable d T i) _ (frame_norm_set_measurable d T) hnorm
  filter_upwards [hp,hs] with y hy hyNorm
  intro hd q hqV hq
  simpa only [Fintype.card_fin] using invariant_query_total_moment d T
    (V ⊔ Submodule.span ℝ {y}) (b y) (by simpa only [Fintype.card_fin] using hd)
    _ hy hyNorm q hqV hq

end Bilevel.TransportObserver
