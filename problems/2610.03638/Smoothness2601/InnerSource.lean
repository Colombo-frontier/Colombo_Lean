import Smoothness2601.InnerPopulation
import Smoothness2601.InnerCost

/-! Source-facing ordinary-inner solve, including the deterministic sample
budget at any fixed accuracy scale (in particular c = 32 C_y). -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Smoothness2601.InnerSource

theorem scaled_expression {D c ε : ℝ} (hD : 0 ≤ D) (hc : 0 < c)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1/(ε/c) ^ 2 + Real.log (2+D/(ε/c)) ≤
      (1+c ^ 2+max 1 c)*(1/ε ^ 2+Real.log (2+D/ε)) := by
  have hs : 1 ≤ max (1:ℝ) c := le_max_left _ _
  have hsc : c ≤ max (1:ℝ) c := le_max_right _ _
  have hs0 : 0 < max (1:ℝ) c := lt_of_lt_of_le (by norm_num) hs
  have hDε : 0 ≤ D/ε := div_nonneg hD hε.le
  have hM : 0 < 2+D/ε := by positivity
  have hL : 0 ≤ Real.log (2+D/ε) := Real.log_nonneg (by linarith)
  have he : D/(ε/c) = c*(D/ε) := by field_simp; ring
  have harg : 2+D/(ε/c) ≤ max 1 c*(2+D/ε) := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_right hsc hDε
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2+D/(ε/c)) harg
  rw [Real.log_mul hs0.ne' hM.ne'] at hlog
  have hlogs := Real.log_le_sub_one_of_pos hs0
  have hw : 1 ≤ 1/ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hws := mul_le_mul_of_nonneg_left hw hs0.le
  have hwL := mul_nonneg (add_nonneg hc2 hs0.le) hL
  have hinv : 1/(ε/c) ^ 2 = c ^ 2*(1/ε ^ 2) := by field_simp
  rw [hinv]
  nlinarith

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [FiniteDimensional ℝ Y] {b : Budgets}
  (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def costConstant (b : Budgets) (c : ℝ) : ℝ :=
  InnerCost.constant (InnerGeometry.rate b) (InnerGeometry.stepsize b ^ 2*b.σ ^ 2)*
    (1+c ^ 2+max 1 c)

theorem costConstant_pos (b : Budgets) (hgap : b.μ < b.L₁) (c : ℝ) :
    0 < costConstant b c := by
  have hr := InnerGeometry.rate_range b hgap
  have hC := InnerCost.constant_pos hr.1 hr.2 (by positivity :
    0 ≤ InnerGeometry.stepsize b ^ 2*b.σ ^ 2)
  have hs : 1 ≤ max (1:ℝ) c := le_max_left _ _
  unfold costConstant
  apply mul_pos hC
  nlinarith [sq_nonneg c]

theorem sample_budget (hgap : b.μ < b.L₁) {D c ε : ℝ} (hD : 0 ≤ D)
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεc : ε ≤ c) :
    (InnerPopulation.samples b D (ε/c) : ℝ) ≤
      costConstant b c*(1/ε ^ 2+Real.log (2+D/ε)) := by
  have hr := InnerGeometry.rate_range b hgap
  have hA : 0 ≤ InnerGeometry.stepsize b ^ 2*b.σ ^ 2 := by positivity
  have hbound := InnerCost.sample_bound hr.1 hr.2 hA hD (div_pos hε hc)
    ((div_le_one hc).mpr hεc)
  have he := scaled_expression hD hc hε hε1
  have hC := (InnerCost.constant_pos hr.1 hr.2 hA).le
  have hb := hbound.trans (mul_le_mul_of_nonneg_left he hC)
  simpa only [InnerPopulation.samples, InnerSolve.count, InnerSolve.batchCount,
    Nat.cast_sum, costConstant, mul_assoc] using hb

/-- Ordinary inner solution from actual full-gradient calls. The batch sizes,
iteration count and resulting total are fixed from public constants. -/
theorem ordinary_inner_solve (hgap : b.μ < b.L₁) {D c ε : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεc : ε ≤ c)
    (y₀ : Y) (x : X) (h : History) (hinit : ‖y₀-P.yStar x‖ ≤ D) :
    (InnerPopulation.program P O D (ε/c) y₀).CallsEq
      (fun _ => InnerPopulation.samples b D (ε/c)) ∧
    Integrable (fun z => ‖z.1-P.yStar x‖)
      ((InnerPopulation.program P O D (ε/c) y₀).law (x,h)) ∧
    (∫ z, ‖z.1-P.yStar x‖ ∂(InnerPopulation.program P O D (ε/c) y₀).law (x,h)) ≤ ε/c ∧
    (InnerPopulation.samples b D (ε/c) : ℝ) ≤
      costConstant b c*(1/ε ^ 2+Real.log (2+D/ε)) := by
  have hm := InnerPopulation.program_expected_norm P O hgap hD (div_pos hε hc) y₀ x h hinit
  exact ⟨InnerPopulation.program_calls P O _ _ _,hm.1,hm.2,
    sample_budget hgap hD hc hε hε1 hεc⟩

end Smoothness2601.InnerSource
