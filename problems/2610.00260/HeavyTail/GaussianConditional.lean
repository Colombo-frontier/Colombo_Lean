import HeavyTail.GaussianMixture
import Mathlib.Probability.Kernel.Defs

/-!
The conditional-law form of the corrected `lem:mixed-exp`. The past has an
arbitrary measurable state space, and the noise and center laws are genuine
Markov kernels. Conditional independence is represented by the product of
their laws at each history. All moment and ball assumptions may hold only
almost everywhere in the past. The hypothesis `0 ≤ η` is explicit; the
manuscript's literal statement omits this necessary hypothesis.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The same exponential rate holds for almost every past under arbitrary
conditional noise and bounded-center laws satisfying the raw hypotheses. -/
theorem gaussian_conditional_mixture_exp_bound
    (μ : Measure H) (κ : Kernel H Ω) [IsMarkovKernel κ]
    (Q : Kernel H E) [IsMarkovKernel Q]
    (ξ : H → Ω → E) (hξ : ∀ h, Measurable (ξ h))
    (b x c : H → E) {p s V M R η a : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (h2 : ∀ᵐ h ∂μ, Integrable (fun ω => ‖ξ h ω‖ ^ 2) (κ h))
    (hcenter : ∀ᵐ h ∂μ, (∫ ω, ξ h ω ∂κ h) = 0)
    (hV : ∀ᵐ h ∂μ, (∫ ω, ‖ξ h ω‖ ^ 2 ∂κ h) ≤ V)
    (hweak : ∀ᵐ h ∂μ, ∀ v : E, ‖v‖ = 1 →
      (∫ ω, |⟪v, ξ h ω⟫_ℝ| ^ p ∂κ h) ≤ s ^ p)
    (hb : ∀ᵐ h ∂μ, ‖b h‖ ≤ M) (hx : ∀ᵐ h ∂μ, ‖x h - c h‖ ≤ R)
    (hQ : ∀ᵐ h ∂μ, ∀ᵐ z ∂Q h, ‖z - c h‖ ≤ R)
    (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    ∀ᵐ h ∂μ,
      Integrable (mixtureExp E (ξ h) (b h) (x h) η a ε)
        ((Q h).prod ((κ h).prod (euclideanGaussianLaw E))) ∧
      (∫ w, mixtureExp E (ξ h) (b h) (x h) η a ε w
        ∂(Q h).prod ((κ h).prod (euclideanGaussianLaw E))) ≤
        Real.exp (mixedConstant p *
          (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  filter_upwards [h2, hcenter, hV, hweak, hb, hx, hQ] with h h2h hch hVh hwh hbh hxh hQh
  exact gaussian_ball_mixture_exp_bound E (hξ h) h2h hch hp hp2 hs hVh hwh
    (b h) (x h) (c h) hbh hxh hη ha haR htune (Q h) hQh ε hε

end HeavyTail.GaussianEstimates
