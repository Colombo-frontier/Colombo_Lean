import HeavyTail.GaussianOnlineStabilityFactors

/-! A measurable concrete online update and its pathwise master inequality.
Inactive rounds freeze the mixture and contribute exactly zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def gaussianOnlineUpdate (c : E) (a η β : ℝ) (centers : ι → E)
    {ε : ℝ} (hε : 0 < ε) : SimplexPoint ι × E → SimplexPoint ι :=
  fun p => (gaussian_observation_update_exists E c a η β centers hε).choose (p.2, p.1)

theorem gaussianOnlineUpdate_measurable (c : E) (a η β : ℝ) (centers : ι → E)
    {ε : ℝ} (hε : 0 < ε) : Measurable (gaussianOnlineUpdate E c a η β centers hε) :=
  (gaussian_observation_update_exists E c a η β centers hε).choose_spec.1.comp measurable_swap

abbrev gaussianOnlineGenerator (c : E) (a β : ℝ) (centers : ι → E) : (ι → ℝ) → ℝ :=
  gaussianMixtureGenerator E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers)

abbrev gaussianOnlineDerivative (c : E) (a β : ℝ) (centers : ι → E) :=
  gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers)

abbrev gaussianOnlineDivergence (c : E) (a β : ℝ) (centers : ι → E) (q w : ι → ℝ) : ℝ :=
  bregmanDivergence (gaussianOnlineGenerator E c a β centers)
    (gaussianOnlineDerivative E c a β centers) q w

theorem gaussianOnlineUpdate_step (c : E) {a η β M : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hM : 0 ≤ M)
    (centers : ι → E) {ε : ℝ} (hε : 0 < ε)
    (p : SimplexPoint ι) {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι)
    (Y b : E) (hb : ‖b‖ ≤ M) :
    gaussianOnlineDivergence E c a β centers q
        (gaussianOnlineUpdate E c a η β centers hε (p, Y)).val +
      η * ⟪b, finiteMixtureMean centers p.val - finiteMixtureMean centers q⟫_ℝ ≤
    gaussianOnlineDivergence E c a β centers q p.val + η ^ 2 * M ^ 2 / (2 * β) +
      Real.log (onlineMixtureW E c a η centers p.val Y b (finiteMixtureMean centers p.val)) +
      (∫ u, onlineMixtureError E η Y b (finiteMixtureMean centers p.val) u
        ∂physicalGaussianMixtureLaw E c a centers q) + ε := by
  have hf := (gaussian_observation_update_exists E c a η β centers hε).choose_spec.2
    (Y, p) q hq
  have hstep := approximate_mirror_update (H := gaussianOnlineGenerator E c a β centers)
    (observedClippedLoss E c a η centers (Y, p.val)) hf
  have hs := gaussian_online_stability_bound E c ha hη hβ hM centers
    (gaussianOnlineUpdate E c a η β centers hε (p, Y)).property p.property Y b hb
  have he := onlineMixtureError_integral E c ha η centers hq p.val Y b
  have hinner : ⟪b, finiteMixtureMean centers p.val - finiteMixtureMean centers q⟫_ℝ =
      -⟪b, finiteMixtureMean centers q - finiteMixtureMean centers p.val⟫_ℝ := by
    simp only [inner_sub_right]
    ring
  change gaussianOnlineDivergence E c a β centers q
      (gaussianOnlineUpdate E c a η β centers hε (p, Y)).val ≤ _ at hstep
  rw [hinner]
  dsimp only [gaussianOnlineDivergence, gaussianOnlineGenerator, gaussianOnlineDerivative,
    gaussianOnlineUpdate] at hstep hs ⊢
  linarith only [hstep, hs, he]

theorem gaussianOnlineDivergence_nonneg (c : E) (a : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (centers : ι → E) {q w : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) (hw : w ∈ stdSimplex ℝ ι) :
    0 ≤ gaussianOnlineDivergence E c a β centers q w :=
  bregmanDivergence_nonneg
    (gaussian_mixture_generator_convex E _ hβ (finiteMixtureMean centers)) hw hq
    (gaussian_mixture_generator_derivative E _ β (finiteMixtureMean centers) hw)

/-- Arbitrary raw rounds may be inactive. Only actual updates incur loss and error. -/
theorem gaussian_online_masked_master (c : E) {a η β M : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hM : 0 ≤ M)
    (centers : ι → E) {ε : ℝ} (hε : 0 < ε)
    (w : ℕ → SimplexPoint ι) (Y b : ℕ → E) (active : ℕ → Bool)
    (hrec : ∀ k, w (k + 1) = if active k then
      gaussianOnlineUpdate E c a η β centers hε (w k, Y k) else w k)
    (hb : ∀ k, ‖b k‖ ≤ M) {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (n : ℕ) :
    (∑ k ∈ Finset.range n, if active k then
      η * ⟪b k, finiteMixtureMean centers (w k).val - finiteMixtureMean centers q⟫_ℝ else 0) ≤
    gaussianOnlineDivergence E c a β centers q (w 0).val +
      ∑ k ∈ Finset.range n, if active k then
        η ^ 2 * M ^ 2 / (2 * β) +
        Real.log (onlineMixtureW E c a η centers (w k).val (Y k) (b k)
          (finiteMixtureMean centers (w k).val)) +
        (∫ u, onlineMixtureError E η (Y k) (b k) (finiteMixtureMean centers (w k).val) u
          ∂physicalGaussianMixtureLaw E c a centers q) + ε else 0 := by
  let loss : ℕ → ℝ := fun k => if active k then
    η * ⟪b k, finiteMixtureMean centers (w k).val - finiteMixtureMean centers q⟫_ℝ else 0
  let cost : ℕ → ℝ := fun k => if active k then
    η ^ 2 * M ^ 2 / (2 * β) +
    Real.log (onlineMixtureW E c a η centers (w k).val (Y k) (b k)
      (finiteMixtureMean centers (w k).val)) +
    (∫ u, onlineMixtureError E η (Y k) (b k) (finiteMixtureMean centers (w k).val) u
      ∂physicalGaussianMixtureLaw E c a centers q) + ε else 0
  have hstep (k : ℕ) : gaussianOnlineDivergence E c a β centers q (w (k + 1)).val + loss k ≤
      gaussianOnlineDivergence E c a β centers q (w k).val + cost k := by
    rw [hrec k]
    cases hk : active k with
    | false => simp [loss, cost, hk]
    | true =>
      simpa [loss, cost, hk, add_assoc] using
        gaussianOnlineUpdate_step E c ha hη hβ hM centers hε (w k) hq (Y k) (b k) (hb k)
  have htel : ∀ n, gaussianOnlineDivergence E c a β centers q (w n).val +
      (∑ k ∈ Finset.range n, loss k) ≤ gaussianOnlineDivergence E c a β centers q (w 0).val +
      ∑ k ∈ Finset.range n, cost k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [hstep N]
  have hpos := gaussianOnlineDivergence_nonneg E c a hβ.le centers hq (w n).property
  have htelN := htel n
  change (∑ k ∈ Finset.range n, loss k) ≤ _
  linarith

end HeavyTail.GaussianEntropy
