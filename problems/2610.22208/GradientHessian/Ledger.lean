import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The mixed-query ledger: its algebraic and probabilistic consequence

This module formalizes the final ledger-to-probability step in Theorem
`thm:ledger-log` of the supplied manuscript. It does not construct the hard
input law, the comparison oracle, or the two task-count random variables.
Their pointwise ledger, integrability, and expectation estimates are explicit
hypotheses. In particular, this is not a proof of the manuscript's main lower
bound.
-/

namespace GradientHessian.Ledger

open MeasureTheory

/-- The deterministic task ledger and the two budget caps force at least
one quarter of all tasks into early completions or repairs. -/
theorem exceptional_tasks_lower_bound
    {n M h G ell early repair : ℝ}
    (hM : 0 ≤ M) (hell : 0 < ell)
    (hrich : h ≤ n / 2) (hordinary : G + 1 ≤ n * M * ell / 4)
    (hledger : n * M ≤ h * M + (G + 1) / ell + early + repair) :
    n * M / 4 ≤ early + repair := by
  have hrich' : h * M ≤ n * M / 2 := by
    have := mul_le_mul_of_nonneg_right hrich hM
    nlinarith
  have hord' : (G + 1) / ell ≤ n * M / 4 := by
    apply (div_le_iff₀ hell).2
    nlinarith [hordinary]
  linarith

/-- A direct Markov consequence for actual real-valued random variables.
`success` is an event, and the conclusion is its probability under `μ`.
The proof uses the Bochner integrals of `early` and `repair`; no abstract
probability axioms or free numerical expectation symbols are introduced. -/
theorem success_probability_le_one_thirty_second
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (success : Set Ω) (early repair : Ω → ℝ)
    {n M h G ell : ℝ}
    (hn : 0 < n) (hM : 0 < M) (hell : 0 < ell)
    (hrich : h ≤ n / 2) (hordinary : G + 1 ≤ n * M * ell / 4)
    (hearly_nonneg : ∀ ω, 0 ≤ early ω)
    (hrepair_nonneg : ∀ ω, 0 ≤ repair ω)
    (hearly_int : Integrable early μ) (hrepair_int : Integrable repair μ)
    (hearly_mean : ∫ ω, early ω ∂μ ≤ n * M / 256)
    (hrepair_mean : ∫ ω, repair ω ∂μ ≤ n * M / 256)
    (hledger : ∀ ω ∈ success,
      n * M ≤ h * M + (G + 1) / ell + early ω + repair ω) :
    μ.real success ≤ 1 / 32 := by
  have hNM : 0 < n * M := mul_pos hn hM
  have hcontain : success ⊆ {ω | n * M / 4 ≤ early ω + repair ω} := by
    intro ω hω
    exact exceptional_tasks_lower_bound hM.le hell hrich hordinary (hledger ω hω)
  have hsum_nonneg : 0 ≤ᵐ[μ] (fun ω => early ω + repair ω) :=
    Filter.Eventually.of_forall fun ω => add_nonneg (hearly_nonneg ω) (hrepair_nonneg ω)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hsum_nonneg
    (hearly_int.add hrepair_int) (n * M / 4)
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hcontain)
    (by positivity : 0 ≤ n * M / 4)
  have hsum_mean : (∫ ω, early ω + repair ω ∂μ) ≤ n * M / 128 := by
    rw [integral_add hearly_int hrepair_int]
    linarith
  have hbound : n * M / 4 * μ.real success ≤ n * M / 128 :=
    hmono.trans (hmarkov.trans hsum_mean)
  nlinarith

end GradientHessian.Ledger
