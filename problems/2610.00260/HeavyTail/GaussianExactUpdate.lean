import HeavyTail.SimplexExactOptimizer
import HeavyTail.GaussianMeasurableUpdate

/-! Exact measurable Gaussian mixture mirror minimizers. The map is measurable
jointly in the observed linear loss and the current simplex point. A physical
observed-vector specialization is given as well. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators InnerProductSpace
namespace HeavyTail

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem mirror_objective_convex {S : Set W} {H : W → ℝ}
    {dH : W → W →L[ℝ] ℝ} (hH : ConvexOn ℝ S H)
    (L : W →L[ℝ] ℝ) (x : W) :
    ConvexOn ℝ S (fun z => L z + bregmanDivergence H dH z x) := by
  have hbase := (((L - dH x).toLinearMap.convexOn hH.1).add hH).add_const (dH x x - H x)
  convert hbase using 1
  funext z
  change L z + (H z - H x - dH x (z - x)) =
    (L z - dH x z + H z) + (dH x x - H x)
  rw [map_sub]
  ring

namespace GaussianEntropy

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem gaussian_measurable_exact_optimizer_exists
    (t : ι → E) {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V) :
    ∃ update : ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ p, IsMinOn
        (fun z => p.1 z + bregmanDivergence (gaussianMixtureGenerator E t β M)
          (gaussianMixtureGeneratorDerivative E t β M) z p.2.val)
        (stdSimplex ℝ ι) (update p).val := by
  let H := gaussianMixtureGenerator E t β M
  let dH := gaussianMixtureGeneratorDerivative E t β M
  let P := ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι
  let F : P → (ι → ℝ) → ℝ := fun p z => p.1 z + bregmanDivergence H dH z p.2.val
  let dF : P → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ := fun p z => p.1 + dH z - dH p.2.val
  have hconv : ∀ p, ConvexOn ℝ (stdSimplex ℝ ι) (F p) := by
    intro p
    exact mirror_objective_convex (gaussian_mixture_generator_convex E t hβ M) p.1 p.2.val
  have hd : ∀ p w, w ∈ stdSimplex ℝ ι →
      HasFDerivWithinAt (F p) (dF p w) (stdSimplex ℝ ι) w := by
    intro p w hw
    exact mirror_objective_derivative p.1 (gaussian_mixture_generator_derivative E t β M hw)
  have hc : ∀ p, ContinuousOn (dF p) (stdSimplex ℝ ι) := by
    intro p
    exact (continuousOn_const.add (gaussian_mixture_generator_derivative_continuous E t β M)).sub
      continuousOn_const
  have hm : ∀ w ∈ stdSimplex ℝ ι, Measurable (fun p : P => dF p w) := by
    intro w _hw
    exact (measurable_fst.add_const (dH w)).sub
      (((gaussian_mixture_generator_derivative_continuous E t β M).restrict.measurable).comp
        measurable_snd)
  obtain ⟨u, hu, humem, hmin⟩ := exists_measurable_simplex_exact_optimizer F dF hconv hd hc hm
  exact ⟨fun p => ⟨u p, humem p⟩, hu.subtype_mk, hmin⟩

theorem gaussian_measurable_exact_mirror_update_exists
    (t : ι → E) {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V) :
    ∃ update : ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ p q, q ∈ stdSimplex ℝ ι →
        bregmanDivergence (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) q (update p).val ≤
          bregmanDivergence (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) q p.2.val + p.1 q +
          mirrorStability (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) p.1 p.2.val (update p).val := by
  obtain ⟨u, hu, hmin⟩ := gaussian_measurable_exact_optimizer_exists E t hβ M
  refine ⟨u, hu, ?_⟩
  intro p q hq
  exact gaussian_mixture_mirror_update E t β M p.1 (u p).property hq (hmin p)

variable [MeasurableSpace V] [BorelSpace V]

/-- Exact optimizer jointly measurable in the physically observed vector Y
and the current mixture weights. The entropy/KL is the actual Gaussian one. -/
theorem gaussian_observation_exact_optimizer_exists
    (t : ι → E) {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V) (η : ℝ) :
    ∃ update : V × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ p, IsMinOn
        (fun z => η * ⟪p.1, M z⟫_ℝ + bregmanDivergence (gaussianMixtureGenerator E t β M)
          (gaussianMixtureGeneratorDerivative E t β M) z p.2.val)
        (stdSimplex ℝ ι) (update p).val := by
  let L : V → (ι → ℝ) →L[ℝ] ℝ := fun Y => η • (innerSL ℝ Y).comp M
  have hL : Continuous L := ((innerSL ℝ).continuous.clm_comp_const M).const_smul η
  obtain ⟨u, hu, hmin⟩ := gaussian_measurable_exact_optimizer_exists E t hβ M
  refine ⟨fun p => u (L p.1, p.2), hu.comp ((hL.measurable.comp measurable_fst).prodMk measurable_snd), ?_⟩
  intro p
  simpa only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    innerSL_apply] using hmin (L p.1, p.2)

/-- The same exact measurable map minimizes the explicit Gaussian KL plus
quadratic-mean objective, not merely an abstract Bregman expression. -/
theorem gaussian_observation_exact_KL_optimizer_exists
    (t : ι → E) {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V) (η : ℝ) :
    ∃ update : V × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ p, IsMinOn
        (fun z => η * ⟪p.1, M z⟫_ℝ +
          densityRelativeEntropy (GaussianEstimates.euclideanGaussianLaw E)
            (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) z)
            (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) p.2.val) +
          β / 2 * ‖M z - M p.2.val‖ ^ 2)
        (stdSimplex ℝ ι) (update p).val := by
  obtain ⟨u, hu, hmin⟩ := gaussian_observation_exact_optimizer_exists E t hβ M η
  refine ⟨u, hu, ?_⟩
  intro p z hz
  have h := hmin p hz
  change η * ⟪p.1, M (u p).val⟫_ℝ +
    bregmanDivergence (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M) (u p).val p.2.val ≤
    η * ⟪p.1, M z⟫_ℝ + bregmanDivergence (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M) z p.2.val at h
  rw [gaussian_mixture_generator_bregman E t β M (u p).property p.2.property,
    gaussian_mixture_generator_bregman E t β M hz p.2.property] at h
  simpa only [add_assoc] using h

end GaussianEntropy
end HeavyTail
