import HeavyTail.GaussianMixedBound

/-!
Full Gaussian-mixture exponential inequality for the independent product law
of a centered oracle noise, an arbitrary bounded-center probability law, and
a standard Gaussian. This is `lem:mixed-exp` with the necessary explicit
nonnegative-learning-rate hypothesis. No exponential-moment conclusion is
assumed; raw second and unit-direction p-th moments are the inputs.
-/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def mixtureExp (ξ : Ω → E) (b x : E) (η a ε : ℝ) (w : E × (Ω × E)) : ℝ :=
  fixedMixedExp E ξ b (w.1 - x) η a ε w.2

theorem gaussian_mixture_exp_bound {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p s V M R η a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (b x : E) (hb : ‖b‖ ≤ M)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (Q : Measure E) [IsProbabilityMeasure Q] (hQ : ∀ᵐ z ∂Q, ‖z - x‖ ≤ 2 * R)
    (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Integrable (mixtureExp E ξ b x η a ε) (Q.prod (P.prod (euclideanGaussianLaw E))) ∧
    (∫ w, mixtureExp E ξ b x η a ε w ∂Q.prod (P.prod (euclideanGaussianLaw E))) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  let F := mixtureExp E ξ b x η a ε
  let K := Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2)))
  have hf : StronglyMeasurable F := by
    apply Measurable.stronglyMeasurable
    unfold F mixtureExp fixedMixedExp HeavyTail.clip
    fun_prop
  have hfi (z : E) : Integrable (fun w => F (z, w)) (P.prod (euclideanGaussianLaw E)) :=
    fixedMixedExp_integrable E hξ b (z - x) η a ε hε
  have hpos (w : E × (Ω × E)) : 0 ≤ F w := (Real.exp_pos _).le
  have hbound : ∀ᵐ z ∂Q, (∫ w, F (z, w) ∂P.prod (euclideanGaussianLaw E)) ≤ K := by
    filter_upwards [hQ] with z hz
    exact fixed_mixed_exp_bound E hξ h2 hcenter hp hp2 hs hV hweak b (z - x)
      hb hz hη ha haR htune ε hε
  have houter : Integrable (fun z => ∫ w, ‖F (z, w)‖ ∂P.prod (euclideanGaussianLaw E)) Q := by
    apply (integrable_const K).mono' hf.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
    have he : (fun w => ‖F (z, w)‖) = (fun w => F (z, w)) := by
      funext w
      exact Real.norm_of_nonneg (hpos (z, w))
    rw [he]
    exact hz
  have hi : Integrable F (Q.prod (P.prod (euclideanGaussianLaw E))) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr ⟨ae_of_all _ hfi, houter⟩
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have h := integral_mono_ae hi.integral_prod_left (integrable_const K) hbound
  simpa using h

/-- Exact ball geometry of the manuscript: both x and the mixture centers
lie in the same radius-R ball. -/
theorem gaussian_ball_mixture_exp_bound {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p s V M R η a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (b x c : E) (hb : ‖b‖ ≤ M) (hx : ‖x - c‖ ≤ R)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (Q : Measure E) [IsProbabilityMeasure Q] (hQ : ∀ᵐ z ∂Q, ‖z - c‖ ≤ R)
    (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Integrable (mixtureExp E ξ b x η a ε) (Q.prod (P.prod (euclideanGaussianLaw E))) ∧
    (∫ w, mixtureExp E ξ b x η a ε w ∂Q.prod (P.prod (euclideanGaussianLaw E))) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  apply gaussian_mixture_exp_bound E hξ h2 hcenter hp hp2 hs hV hweak b x hb
    hη ha haR htune Q _ ε hε
  filter_upwards [hQ] with z hz
  have he : z - x = (z - c) - (x - c) := by abel
  rw [he]
  exact (norm_sub_le (z - c) (x - c)).trans (by linarith)

end HeavyTail.GaussianEstimates
