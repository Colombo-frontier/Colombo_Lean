import HeavyTail.GaussianMixtureOptimizer
import HeavyTail.SimplexApproxOptimizer

/-!
# Measurable Gaussian mixture mirror updates

Dominated convergence proves continuity of the actual entropy derivative even
at simplex boundary points. Applying the dense first-order selector gives an
update measurable in the observed linear loss and the previous mixture, with
the requested positive first-order tolerance.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem exponential_entropy_derivative_continuous {μ : Measure Ω}
    {r : ι → Ω → ℝ} (hr : ∀ i, Measurable (r i))
    (hB : Integrable (entropyEnvelope r) μ) :
    ContinuousOn (mixtureEntropyDerivative μ (exponentialComponents r)) (stdSimplex ℝ ι) := by
  apply continuousOn_of_dominated
  · intro w hw
    exact (exponential_entropy_regular hr hB hw).2.aestronglyMeasurable
  · intro w hw
    exact ae_of_all _ (exponential_entropy_differential_bound r hw)
  · exact hB
  · apply ae_of_all
    intro ω w hw
    exact (((mixtureLinear (exponentialComponents r) ω).continuous.continuousWithinAt.log
      (mixtureDensity_pos (fun _i _ω => Real.exp_pos _) hw ω).ne').add_const 1).smul
        continuousWithinAt_const

namespace GaussianEntropy

open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem gaussian_mixture_entropy_derivative_continuous (t : ι → E) :
    ContinuousOn
      (mixtureEntropyDerivative (euclideanGaussianLaw E)
        (fun i => gaussianExponentialDensity E (t i))) (stdSimplex ℝ ι) :=
  exponential_entropy_derivative_continuous (fun i => gaussianLogDensity_measurable E (t i))
    (gaussian_entropyEnvelope_integrable E t)

theorem gaussian_mixture_generator_derivative_continuous (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) :
    ContinuousOn (gaussianMixtureGeneratorDerivative E t β M) (stdSimplex ℝ ι) := by
  have hquad : Continuous (fun w : ι → ℝ => β • (innerSL ℝ (M w)).comp M) :=
    (((innerSL ℝ).continuous.comp M.continuous).clm_comp_const M).const_smul β
  exact (gaussian_mixture_entropy_derivative_continuous E t).add hquad.continuousOn

variable [Nonempty ι]

/-- No optimizer or residual premise: the measurable update is constructed. -/
theorem gaussian_measurable_first_order_update_exists
    (t : ι → E) (β : ℝ) (M : (ι → ℝ) →L[ℝ] V) {ε : ℝ} (hε : 0 < ε) :
    ∃ update : ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ p q, q ∈ stdSimplex ℝ ι →
        -ε ≤ (p.1 + gaussianMixtureGeneratorDerivative E t β M (update p).val -
          gaussianMixtureGeneratorDerivative E t β M p.2.val) (q - (update p).val) := by
  let H := gaussianMixtureGenerator E t β M
  let dH := gaussianMixtureGeneratorDerivative E t β M
  let P := ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι
  let F : P → (ι → ℝ) → ℝ := fun p z => p.1 z + bregmanDivergence H dH z p.2.val
  let dF : P → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ := fun p z => p.1 + dH z - dH p.2.val
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
  obtain ⟨u, hu, humem, hfirst⟩ := exists_measurable_simplex_first_order_optimizer
    F dF hd hc hm (fun _ => ε) measurable_const (fun _ => hε)
  refine ⟨fun p => ⟨u p, humem p⟩, hu.subtype_mk, ?_⟩
  exact hfirst

/-- The constructed measurable update has the approximate Bregman inequality. -/
theorem gaussian_measurable_mirror_update_exists
    (t : ι → E) (β : ℝ) (M : (ι → ℝ) →L[ℝ] V) {ε : ℝ} (hε : 0 < ε) :
    ∃ update : ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ p q, q ∈ stdSimplex ℝ ι →
        bregmanDivergence (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) q (update p).val ≤
          bregmanDivergence (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) q p.2.val + p.1 q +
          mirrorStability (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) p.1 p.2.val (update p).val + ε := by
  obtain ⟨u, hu, hfirst⟩ := gaussian_measurable_first_order_update_exists E t β M hε
  exact ⟨u, hu, fun p q hq => approximate_mirror_update p.1 (hfirst p q hq)⟩

/-- Every trajectory of the constructed update satisfies the approximate regret bound. -/
theorem gaussian_measurable_regret_update_exists
    (t : ι → E) {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ update : ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι → SimplexPoint ι,
      Measurable update ∧ ∀ (x : ℕ → SimplexPoint ι) (L : ℕ → (ι → ℝ) →L[ℝ] ℝ)
        (q : ι → ℝ), q ∈ stdSimplex ℝ ι →
        (∀ k, x (k + 1) = update (L k, x k)) → ∀ n : ℕ,
        -(∑ k ∈ Finset.range n, L k q) ≤
          densityRelativeEntropy (euclideanGaussianLaw E)
            (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) q)
            (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) (x 0).val) +
          β / 2 * ‖M q - M (x 0).val‖ ^ 2 +
          (∑ k ∈ Finset.range n, mirrorStability (gaussianMixtureGenerator E t β M)
            (gaussianMixtureGeneratorDerivative E t β M) (L k) (x k).val (x (k + 1)).val) + n * ε := by
  obtain ⟨u, hu, hfirst⟩ := gaussian_measurable_first_order_update_exists E t β M hε
  refine ⟨u, hu, ?_⟩
  intro x L q hq hrec n
  have hf : ∀ k, -ε ≤
      (L k + gaussianMixtureGeneratorDerivative E t β M (x (k + 1)).val -
        gaussianMixtureGeneratorDerivative E t β M (x k).val) (q - (x (k + 1)).val) := by
    intro k
    rw [hrec k]
    exact hfirst (L k, x k) q hq
  have h := approximate_mirror_regret (gaussian_mixture_generator_convex E t hβ M)
    (fun k => (x k).property) hq
    (fun w hw => gaussian_mixture_generator_derivative E t β M hw) hf n
  rwa [gaussian_mixture_generator_bregman E t β M hq (x 0).property] at h

end GaussianEntropy
end HeavyTail
