import HeavyTail.GaussianExactClippedUpdate

/-! Strict convexity in the mixture density and uniqueness of the minimizing
density. Mixture weights need not be unique and components may coincide. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace HeavyTail

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- Entropy has strict Jensen inequality whenever the two induced densities
differ modulo the reference measure. No linear independence is required. -/
theorem mixtureEntropy_strict_density {φ : ι → Ω → ℝ}
    (hφ : ∀ i ω, 0 < φ i ω)
    (hent : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ w) μ)
    {x y : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hne : ¬ mixtureDensity φ x =ᵐ[μ] mixtureDensity φ y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    mixtureEntropy μ φ (a • x + b • y) <
      a * mixtureEntropy μ φ x + b * mixtureEntropy μ φ y := by
  have hxy := (convex_stdSimplex ℝ ι) hx hy ha.le hb.le hab
  let f := mixtureEntropyIntegrand φ (a • x + b • y)
  let g := fun ω => a * mixtureEntropyIntegrand φ x ω + b * mixtureEntropyIntegrand φ y ω
  have hf : Integrable f μ := hent _ hxy
  have hg : Integrable g μ := ((hent x hx).const_mul a).add ((hent y hy).const_mul b)
  have hle (ω : Ω) : f ω ≤ g ω := by
    have hh := Real.convexOn_mul_log.2
      (show mixtureDensity φ x ω ∈ Ici (0 : ℝ) from (mixtureDensity_pos hφ hx ω).le)
      (show mixtureDensity φ y ω ∈ Ici (0 : ℝ) from (mixtureDensity_pos hφ hy ω).le)
      ha.le hb.le hab
    simpa only [f, g, mixtureEntropyIntegrand, mixtureDensity, map_add, map_smul, smul_eq_mul] using hh
  have hineq := integral_mono hf hg hle
  have hneq : (∫ ω, f ω ∂μ) ≠ ∫ ω, g ω ∂μ := by
    intro heq
    have heqae := (integral_eq_iff_of_ae_le hf hg (Filter.Eventually.of_forall hle)).mp heq
    apply hne
    filter_upwards [heqae] with ω hω
    by_contra hdiff
    have hh := Real.strictConvexOn_mul_log.2
      (show mixtureDensity φ x ω ∈ Ici (0 : ℝ) from (mixtureDensity_pos hφ hx ω).le)
      (show mixtureDensity φ y ω ∈ Ici (0 : ℝ) from (mixtureDensity_pos hφ hy ω).le)
      hdiff ha hb hab
    have hlt : f ω < g ω := by
      simpa only [f, g, mixtureEntropyIntegrand, mixtureDensity, map_add, map_smul, smul_eq_mul] using hh
    exact (ne_of_lt hlt) hω
  have hstrict : (∫ ω, f ω ∂μ) < ∫ ω, g ω ∂μ := by
    rcases eq_or_lt_of_le hineq with h | h
    · exact False.elim (hneq h)
    · exact h
  change mixtureEntropy μ φ (a • x + b • y) <
    ∫ ω, a * mixtureEntropyIntegrand φ x ω + b * mixtureEntropyIntegrand φ y ω ∂μ at hstrict
  rw [integral_add ((hent x hx).const_mul a) ((hent y hy).const_mul b),
    integral_const_mul, integral_const_mul] at hstrict
  exact hstrict

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem mixtureMirror_strict_density {φ : ι → Ω → ℝ}
    (hφ : ∀ i ω, 0 < φ i ω)
    (hent : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ w) μ)
    {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V)
    (L : (ι → ℝ) →L[ℝ] ℝ) (w : ι → ℝ)
    {x y : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hne : ¬ mixtureDensity φ x =ᵐ[μ] mixtureDensity φ y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    let F := fun z => L z + bregmanDivergence (meanRegularizedEntropy μ φ β M)
      (meanRegularizedEntropyDerivative μ φ β M) z w
    F (a • x + b • y) < a * F x + b * F y := by
  let H := meanRegularizedEntropy μ φ β M
  let dH := meanRegularizedEntropyDerivative μ φ β M
  let C := fun z => (L - dH w) z + β / 2 * ‖M z‖ ^ 2 + (dH w w - H w)
  have hC : ConvexOn ℝ (stdSimplex ℝ ι) C :=
    (((L - dH w).toLinearMap.convexOn (convex_stdSimplex ℝ ι)).add
      (meanPenalty_convex (convex_stdSimplex ℝ ι) hβ M)).add_const (dH w w - H w)
  have hformula (z : ι → ℝ) :
      L z + bregmanDivergence H dH z w = mixtureEntropy μ φ z + C z := by
    change L z + (H z - H w - dH w (z - w)) = _
    rw [map_sub]
    dsimp only [H, meanRegularizedEntropy, C, ContinuousLinearMap.sub_apply]
    ring
  change L (a • x + b • y) + bregmanDivergence H dH (a • x + b • y) w <
    a * (L x + bregmanDivergence H dH x w) + b * (L y + bregmanDivergence H dH y w)
  rw [hformula, hformula, hformula]
  have he := mixtureEntropy_strict_density hφ hent hx hy hne ha hb hab
  have hc := hC.2 hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hc
  nlinarith only [he, hc]

theorem mixtureMirror_minimizing_density_unique {φ : ι → Ω → ℝ}
    (hφ : ∀ i ω, 0 < φ i ω)
    (hent : ∀ w ∈ stdSimplex ℝ ι, Integrable (mixtureEntropyIntegrand φ w) μ)
    {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V)
    (L : (ι → ℝ) →L[ℝ] ℝ) (w : ι → ℝ)
    {x y : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hminx : IsMinOn (fun z => L z + bregmanDivergence (meanRegularizedEntropy μ φ β M)
      (meanRegularizedEntropyDerivative μ φ β M) z w) (stdSimplex ℝ ι) x)
    (hminy : IsMinOn (fun z => L z + bregmanDivergence (meanRegularizedEntropy μ φ β M)
      (meanRegularizedEntropyDerivative μ φ β M) z w) (stdSimplex ℝ ι) y) :
    mixtureDensity φ x =ᵐ[μ] mixtureDensity φ y := by
  by_contra hne
  have hh := mixtureMirror_strict_density hφ hent hβ M L w hx hy hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ stdSimplex ℝ ι :=
    (convex_stdSimplex ℝ ι) hx hy (by norm_num) (by norm_num) (by norm_num)
  let F := fun z => L z + bregmanDivergence (meanRegularizedEntropy μ φ β M)
    (meanRegularizedEntropyDerivative μ φ β M) z w
  have hxmid : F x ≤ F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := hminx hmid
  have hymid : F y ≤ F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := hminy hmid
  dsimp only at hh
  change F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) < (1 / 2 : ℝ) * F x + (1 / 2 : ℝ) * F y at hh
  linarith only [hh, hxmid, hymid]

namespace GaussianEntropy

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_mirror_strict_density (t : ι → E) {β : ℝ} (hβ : 0 ≤ β)
    (M : (ι → ℝ) →L[ℝ] V) (L : (ι → ℝ) →L[ℝ] ℝ) (w : ι → ℝ)
    {x y : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hne : ¬ mixtureDensity (fun i => gaussianExponentialDensity E (t i)) x =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
      mixtureDensity (fun i => gaussianExponentialDensity E (t i)) y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    let F := fun z => L z + bregmanDivergence (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M) z w
    F (a • x + b • y) < a * F x + b * F y :=
  mixtureMirror_strict_density (fun _ _ => Real.exp_pos _)
    (fun z hz => (gaussian_mixture_entropy_regular E t hz).1) hβ M L w hx hy hne ha hb hab

theorem gaussian_mirror_minimizing_density_unique (t : ι → E) {β : ℝ} (hβ : 0 ≤ β)
    (M : (ι → ℝ) →L[ℝ] V) (L : (ι → ℝ) →L[ℝ] ℝ) (w : ι → ℝ)
    {x y : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hminx : IsMinOn (fun z => L z + bregmanDivergence (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M) z w) (stdSimplex ℝ ι) x)
    (hminy : IsMinOn (fun z => L z + bregmanDivergence (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M) z w) (stdSimplex ℝ ι) y) :
    mixtureDensity (fun i => gaussianExponentialDensity E (t i)) x =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
      mixtureDensity (fun i => gaussianExponentialDensity E (t i)) y :=
  mixtureMirror_minimizing_density_unique (fun _ _ => Real.exp_pos _)
    (fun z hz => (gaussian_mixture_entropy_regular E t hz).1) hβ M L w hx hy hminx hminy

/-- The literal clipped-loss, density-KL, and quadratic-mean update objective. -/
def gaussianClippedMirrorObjective (c : E) (a η β : ℝ) (centers : ι → E)
    (Y : E) (w z : ι → ℝ) : ℝ :=
  (∫ u, clip (η * ⟪Y, u - finiteMixtureMean centers w⟫_ℝ)
    ∂physicalGaussianMixtureLaw E c a centers z) +
    densityRelativeEntropy (GaussianEstimates.euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) z)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) w) +
    β / 2 * ‖finiteMixtureMean centers z - finiteMixtureMean centers w‖ ^ 2

theorem gaussianClippedMirrorObjective_eq_mirror (c : E) (a η β : ℝ) (centers : ι → E)
    (Y : E) {w z : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (hz : z ∈ stdSimplex ℝ ι) :
    gaussianClippedMirrorObjective E c a η β centers Y w z =
      observedClippedLoss E c a η centers (Y, w) z +
        bregmanDivergence
          (gaussianMixtureGenerator E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers))
          (gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
            (finiteMixtureMean centers)) z w := by
  rw [gaussian_mixture_generator_bregman E _ β _ hz hw,
    observedClippedLoss_eq_expectation E c a η centers _ hz]
  simp only [gaussianClippedMirrorObjective, add_assoc]

theorem gaussian_clipped_objective_strict_density (c : E) (a η : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (centers : ι → E) (Y : E)
    {w x y : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hne : ¬ mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x
      =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
        mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r + s = 1) :
    gaussianClippedMirrorObjective E c a η β centers Y w (r • x + s • y) <
      r * gaussianClippedMirrorObjective E c a η β centers Y w x +
      s * gaussianClippedMirrorObjective E c a η β centers Y w y := by
  have hxy := (convex_stdSimplex ℝ ι) hx hy hr.le hs.le hrs
  rw [gaussianClippedMirrorObjective_eq_mirror E c a η β centers Y hw hxy,
    gaussianClippedMirrorObjective_eq_mirror E c a η β centers Y hw hx,
    gaussianClippedMirrorObjective_eq_mirror E c a η β centers Y hw hy]
  exact gaussian_mirror_strict_density E (fun i => a⁻¹ • (centers i - c)) hβ
    (finiteMixtureMean centers) (observedClippedLoss E c a η centers (Y, w)) w hx hy hne hr hs hrs

theorem gaussian_clipped_minimizing_density_unique (c : E) (a η : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (centers : ι → E) (Y : E)
    {w x y : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hminx : IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) x)
    (hminy : IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) y) :
    mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x
      =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
        mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y := by
  by_contra hne
  have hh := gaussian_clipped_objective_strict_density E c a η hβ centers Y hw hx hy hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ stdSimplex ℝ ι :=
    (convex_stdSimplex ℝ ι) hx hy (by norm_num) (by norm_num) (by norm_num)
  let F := gaussianClippedMirrorObjective E c a η β centers Y w
  have hxmid : F x ≤ F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := hminx hmid
  have hymid : F y ≤ F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := hminy hmid
  change F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) < (1 / 2 : ℝ) * F x + (1 / 2 : ℝ) * F y at hh
  linarith only [hh, hxmid, hymid]

theorem physicalGaussianMixtureLaw_density_congr (c : E) (a : ℝ) (centers : ι → E)
    {x y : ι → ℝ}
    (heq : mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x
      =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
        mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y) :
    physicalGaussianMixtureLaw E c a centers x = physicalGaussianMixtureLaw E c a centers y := by
  have hd : densityMeasure (GaussianEstimates.euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x) =
      densityMeasure (GaussianEstimates.euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y) := by
    apply withDensity_congr_ae
    filter_upwards [heq] with z hz
    exact congrArg ENNReal.ofReal hz
  unfold physicalGaussianMixtureLaw
  rw [hd]

/-- Equal densities give the same literal objective. Together with the strict
Jensen inequality this is strict convexity on densities, not on coordinates. -/
theorem gaussianClippedMirrorObjective_density_congr (c : E) {a : ℝ} (ha : a ≠ 0)
    (η β : ℝ) (centers : ι → E) (Y : E) (w : ι → ℝ)
    {x y : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (heq : mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x
      =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
        mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y) :
    gaussianClippedMirrorObjective E c a η β centers Y w x =
      gaussianClippedMirrorObjective E c a η β centers Y w y := by
  have hlaw := physicalGaussianMixtureLaw_density_congr E c a centers heq
  have hmean : finiteMixtureMean centers x = finiteMixtureMean centers y := by
    rw [← physicalGaussianMixtureLaw_mean E c ha centers hx,
      ← physicalGaussianMixtureLaw_mean E c ha centers hy, hlaw]
  have hKL : densityRelativeEntropy (GaussianEstimates.euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) w) =
      densityRelativeEntropy (GaussianEstimates.euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) w) := by
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz]
  unfold gaussianClippedMirrorObjective
  rw [hlaw, hKL, hmean]

theorem gaussian_clipped_minimizing_law_unique (c : E) (a η : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (centers : ι → E) (Y : E)
    {w x y : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι)
    (hminx : IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) x)
    (hminy : IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) y) :
    physicalGaussianMixtureLaw E c a centers x = physicalGaussianMixtureLaw E c a centers y :=
  physicalGaussianMixtureLaw_density_congr E c a centers
    (gaussian_clipped_minimizing_density_unique E c a η hβ centers Y hw hx hy hminx hminy)

/-- The exact measurable optimizer exists, and every other optimizer induces
the same density. This permits repeated centers and nonunique coordinates. -/
theorem gaussian_clipped_unique_minimizing_density_exists [Nonempty ι]
    (c : E) (a η : ℝ) {β : ℝ} (hβ : 0 ≤ β) (centers : ι → E) (Y : E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    ∃ x ∈ stdSimplex ℝ ι,
      IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) x ∧
      ∀ y ∈ stdSimplex ℝ ι,
        IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) y →
        mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) x
          =ᵐ[GaussianEstimates.euclideanGaussianLaw E]
            mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) y := by
  obtain ⟨update, _hupdate, hmin⟩ :=
    gaussian_clipped_observation_exact_KL_optimizer_exists E c a η hβ centers
  let x : SimplexPoint ι := update (Y, ⟨w, hw⟩)
  have hx : IsMinOn (gaussianClippedMirrorObjective E c a η β centers Y w) (stdSimplex ℝ ι) x.val := by
    simpa only [gaussianClippedMirrorObjective] using hmin (Y, (⟨w, hw⟩ : SimplexPoint ι))
  refine ⟨x.val, x.property, hx, ?_⟩
  intro y hy hminy
  exact gaussian_clipped_minimizing_density_unique E c a η hβ centers Y hw x.property hy hx hminy

end GaussianEntropy
end HeavyTail
