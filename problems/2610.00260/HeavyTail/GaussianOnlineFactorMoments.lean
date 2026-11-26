import HeavyTail.GaussianOnlineStabilityMoments

/-! The two actual conditional-concentration factors: the learner's W and
the exponentiated comparator error. The latter uses genuine Jensen. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem comparator_exp_error_le_factor (c : E) (a η : ℝ) (centers : ι → E)
    {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (Y b x : E) :
    Real.exp (∫ u, onlineMixtureError E η Y b x u ∂physicalGaussianMixtureLaw E c a centers q) ≤
      signedOnlineFactor E c a η 1 centers q Y b x := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hq
  have hi := onlineMixtureError_integrable E c a η centers hq Y b x
  have he : Integrable (fun u => Real.exp (onlineMixtureError E η Y b x u))
      (physicalGaussianMixtureLaw E c a centers q) := by
    simpa only [one_mul] using signed_online_error_exp_integrable E c a η 1
      (Or.inr rfl) centers hq Y b x
  have h := density_entropy_variational
    (w := fun _ : E => (1 : ℝ)) (g := onlineMixtureError E η Y b x)
    (fun _ => zero_lt_one) (integrable_const 1) (by simp)
    (by simpa only [one_mul] using hi) (by simp) he
  simp only [one_mul, Real.log_one, integral_zero, sub_zero] at h
  have hpos := integral_exp_pos he
  have hexp := Real.exp_le_exp.mpr h
  rw [Real.exp_log hpos] at hexp
  simpa only [signedOnlineFactor, one_mul] using hexp

theorem comparator_exp_error_measurable {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → E} (hY : Measurable Y) (c : E) (a η : ℝ) (centers : ι → E)
    {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (b x : E) :
    Measurable (fun ω => Real.exp (∫ u, onlineMixtureError E η (Y ω) b x u
      ∂physicalGaussianMixtureLaw E c a centers q)) := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hq
  have hf : StronglyMeasurable (fun p : Ω × E => onlineMixtureError E η (Y p.1) b x p.2) := by
    apply Measurable.stronglyMeasurable
    unfold onlineMixtureError clip
    fun_prop
  exact hf.integral_prod_right'.measurable.exp

variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem onlineMixtureW_moment {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p s V M R η a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (c b x : E) (hb : ‖b‖ ≤ M)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (centers : ι → E) (hc : ∀ i, ‖centers i - x‖ ≤ 2 * R)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    Integrable (fun ω => onlineMixtureW E c a η centers w (b + ξ ω) b x) P ∧
    (∫ ω, onlineMixtureW E c a η centers w (b + ξ ω) b x ∂P) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  simpa only [signedOnlineFactor, neg_one_mul, onlineMixtureW] using
    signed_online_factor_moment E hξ h2 hcenter hp hp2 hs hV hweak c b x hb
      hη ha haR htune centers hc hw (-1) (Or.inl rfl)

theorem comparator_exp_error_moment {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p s V M R η a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (c b x : E) (hb : ‖b‖ ≤ M)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (centers : ι → E) (hc : ∀ i, ‖centers i - x‖ ≤ 2 * R)
    {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) :
    Integrable (fun ω => Real.exp (∫ u, onlineMixtureError E η (b + ξ ω) b x u
      ∂physicalGaussianMixtureLaw E c a centers q)) P ∧
    (∫ ω, Real.exp (∫ u, onlineMixtureError E η (b + ξ ω) b x u
      ∂physicalGaussianMixtureLaw E c a centers q) ∂P) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  have hf := signed_online_factor_moment E hξ h2 hcenter hp hp2 hs hV hweak c b x hb
    hη ha haR htune centers hc hq 1 (Or.inr rfl)
  have hm := comparator_exp_error_measurable E (P := P) (Y := fun ω => b + ξ ω)
    (measurable_const.add hξ) c a η centers hq b x
  have hi : Integrable (fun ω => Real.exp (∫ u, onlineMixtureError E η (b + ξ ω) b x u
      ∂physicalGaussianMixtureLaw E c a centers q)) P := by
    apply hf.1.mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact comparator_exp_error_le_factor E c a η centers hq (b + ξ ω) b x
  exact ⟨hi, (integral_mono hi hf.1
    (fun ω => comparator_exp_error_le_factor E c a η centers hq (b + ξ ω) b x)).trans hf.2⟩

end HeavyTail.GaussianEntropy
