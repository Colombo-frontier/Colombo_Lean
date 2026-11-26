import FreshGradientMinimax.Multilevel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Iteration of a genuine Markov transition, including propagation of
integrability. A pointwise conditional moment bound gives the finite-horizon
bound for the resulting law; no moments of the trajectory are postulated. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X]

def iterateKernel (K : Kernel X X) : ℕ → Kernel X X
  | 0 => Kernel.id
  | n + 1 => K ∘ₖ iterateKernel K n

instance iterateKernel_markov (K : Kernel X X) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (iterateKernel K n) := by
  induction n with
  | zero => dsimp [iterateKernel]; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (K ∘ₖ iterateKernel K n)
    infer_instance

theorem iterateKernel_integrable (K : Kernel X X) [IsMarkovKernel K]
    (V : X → ℝ) (hV : StronglyMeasurable V) (hpos : ∀ x, 0 ≤ V x)
    (hi : ∀ x, Integrable V (K x)) {r b : ℝ}
    (hstep : ∀ x, (∫ y, V y ∂K x) ≤ r * V x + b) (n : ℕ) (x : X) :
    Integrable V (iterateKernel K n x) := by
  induction n with
  | zero => simpa only [iterateKernel, Kernel.id_apply] using (integrable_dirac' (a := x) hV)
  | succ n ih =>
    have henv : Integrable (fun y => r * V y + b) (iterateKernel K n x) :=
      (ih.const_mul r).add (integrable_const _)
    have hmean : Integrable (fun y => ∫ z, V z ∂K y) (iterateKernel K n x) := by
      apply henv.mono' hV.integral_kernel.aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hpos)]
        exact hstep y)
    change Integrable V ((K ∘ₖ iterateKernel K n) x)
    apply (ProbabilityTheory.integrable_comp_iff hV.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hmean

theorem iterateKernel_recurrence (K : Kernel X X) [IsMarkovKernel K]
    (V : X → ℝ) (hV : StronglyMeasurable V) (hpos : ∀ x, 0 ≤ V x)
    (hi : ∀ x, Integrable V (K x)) {r b : ℝ}
    (hstep : ∀ x, (∫ y, V y ∂K x) ≤ r * V x + b) (n : ℕ) (x : X) :
    (∫ y, V y ∂iterateKernel K (n + 1) x) ≤ r * (∫ y, V y ∂iterateKernel K n x) + b := by
  have hn := iterateKernel_integrable K V hV hpos hi hstep n x
  have hs := iterateKernel_integrable K V hV hpos hi hstep (n + 1) x
  change Integrable V ((K ∘ₖ iterateKernel K n) x) at hs
  change (∫ y, V y ∂(K ∘ₖ iterateKernel K n) x) ≤ _
  rw [Kernel.integral_comp hs]
  have henv : Integrable (fun y => r * V y + b) (iterateKernel K n x) :=
    (hn.const_mul r).add (integrable_const _)
  have hbnd := integral_mono hs.integral_comp henv hstep
  simpa only [integral_add (hn.const_mul r) (integrable_const _), integral_const_mul,
    integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hbnd

theorem iterateKernel_moment (K : Kernel X X) [IsMarkovKernel K]
    (V : X → ℝ) (hV : StronglyMeasurable V) (hpos : ∀ x, 0 ≤ V x)
    (hi : ∀ x, Integrable V (K x)) {r b : ℝ} (hr : 0 ≤ r)
    (hstep : ∀ x, (∫ y, V y ∂K x) ≤ r * V x + b) (n : ℕ) (x : X) :
    (∫ y, V y ∂iterateKernel K n x) ≤ r ^ n * V x + b * ∑ j ∈ Finset.range n, r ^ j := by
  have h := affine_recurrence_bound (p := fun n => ∫ y, V y ∂iterateKernel K n x) hr
    (fun n => iterateKernel_recurrence K V hV hpos hi hstep n x) n
  simpa only [iterateKernel, Kernel.id_apply, integral_dirac' V x hV] using h

end FreshGradientMinimax
