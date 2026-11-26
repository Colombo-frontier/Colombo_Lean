import Smoothness2601.InnerSolve
import Smoothness2601.InnerOracle

/-! A complete ordinary-inner solve for the actual Population and the original
full-gradient Adaptive.Oracle. All queries use the g oracle and all sample
counts are fixed functions of public constants. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Bilevel.Stateful
namespace Smoothness2601.InnerPopulation

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [FiniteDimensional ℝ Y] {b : Budgets}
  (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def program (D u : ℝ) (y₀ : Y) : Procedure X History Y :=
  InnerSolve.scheduled (InnerOracle.blockY P O true) id measurable_id
    (fun _ => y₀) measurable_const (InnerGeometry.stepsize b) (InnerGeometry.rate b) D u

def samples (b : Budgets) (D u : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (InnerSolve.count (InnerGeometry.rate b) D u),
    InnerSolve.batchCount (InnerGeometry.stepsize b) b.σ (InnerGeometry.rate b) D u k

omit [FiniteDimensional ℝ Y] in
theorem program_calls (D u : ℝ) (y₀ : Y) :
    (program P O D u y₀).CallsEq (fun _ => samples b D u) :=
  InnerSolve.scheduled_calls _ _ _ _ _ _ _ _ _

theorem program_mse (hgap : b.μ < b.L₁) {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u)
    (y₀ : Y) (x : X) (h : History) (hinit : ‖y₀-P.yStar x‖ ≤ D) :
    Integrable (fun z => ‖z.1-P.yStar x‖ ^ 2) ((program P O D u y₀).law (x,h)) ∧
    (∫ z, ‖z.1-P.yStar x‖ ^ 2 ∂(program P O D u y₀).law (x,h)) ≤ 3*u ^ 2/4 := by
  have hr := InnerGeometry.rate_range b hgap
  apply InnerSolve.scheduled_mse _ _ _ _ _ (InnerGeometry.stepsize_pos b).ne'
    hr.1 hr.2 hD hu P.yStar _ x h hinit
  intro z y
  change ‖y-InnerGeometry.stepsize b • (InnerOracle.blockY P O true).truth (z,y)-P.yStar z‖ ^ 2 ≤ _
  rw [InnerOracle.lowerY_truth]
  exact InnerGeometry.contraction P z y

theorem program_expected_norm (hgap : b.μ < b.L₁) {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u)
    (y₀ : Y) (x : X) (h : History) (hinit : ‖y₀-P.yStar x‖ ≤ D) :
    Integrable (fun z => ‖z.1-P.yStar x‖) ((program P O D u y₀).law (x,h)) ∧
    (∫ z, ‖z.1-P.yStar x‖ ∂(program P O D u y₀).law (x,h)) ≤ u := by
  have hm := program_mse P O hgap hD hu y₀ x h hinit
  exact InnerSolve.expected_norm_of_mse _ (measurable_fst.sub_const (P.yStar x)).aestronglyMeasurable
    hm.1 hu (hm.2.trans (by nlinarith [sq_nonneg u]))

theorem sample_budget (hgap : b.μ < b.L₁) (D u : ℝ) :
    (samples b D u : ℝ) ≤ InnerSolve.count (InnerGeometry.rate b) D u +
      4*(InnerGeometry.stepsize b ^ 2*b.σ ^ 2)/
        (u ^ 2*(1-Real.sqrt (InnerGeometry.rate b)) ^ 2) :=
  InnerSolve.sample_count_bound _ _ _ _ _ (InnerGeometry.rate_range b hgap).2

/-- Source initialization after a deterministic outer travel bound. -/
theorem initialized_expected_norm (hgap : b.μ < b.L₁) {u R : ℝ}
    (hu : 0 < u) (hR : 0 ≤ R) (x₀ x : X) (y₀ : Y) (h : History)
    (hinit : P.Initialized x₀ y₀) (hdistance : ‖x-x₀‖ ≤ R) :
    (∫ z, ‖z.1-P.yStar x‖ ∂(program P O (b.R₀+(b.L₁/b.μ)*R) u y₀).law (x,h)) ≤ u := by
  apply (program_expected_norm P O hgap (by
    have hr := b.R₀_nonneg
    have hl := b.L₁_pos
    have hm := b.μ_pos
    positivity) hu y₀ x h _).2
  exact InnerGeometry.initial_radius P x₀ x y₀ hinit.inner_error hdistance

end Smoothness2601.InnerPopulation
