import FreshGradientMinimax.Acceleration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Real

/-! Actual Bochner expectations and probability measures (including continuous
noise). These results verify the moment and stopping arguments, not existence
of the full algorithm or the hard distributions. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped InnerProductSpace

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- The variance identity with the actual vector-valued expectation. -/
theorem second_moment_decomposition (e : Ω → E) (he : Integrable e ν)
    (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) ν) :
    (∫ ω, ‖e ω - ∫ t, e t ∂ν‖ ^ 2 ∂ν) + ‖∫ t, e t ∂ν‖ ^ 2 =
      ∫ ω, ‖e ω‖ ^ 2 ∂ν := by
  let b := ∫ t, e t ∂ν
  have hi : Integrable (fun ω => 2 * ⟪b, e ω⟫_ℝ) ν := (he.const_inner b).const_mul 2
  have hc : Integrable (fun _ : Ω => ‖b‖ ^ 2) ν := integrable_const _
  have his : Integrable (fun ω => ‖e ω‖ ^ 2 - 2 * ⟪b, e ω⟫_ℝ) ν := he2.sub hi
  have hn (ω : Ω) : ‖e ω - b‖ ^ 2 = ‖e ω‖ ^ 2 - 2 * ⟪b, e ω⟫_ℝ + ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm (e ω) b]
  change (∫ ω, ‖e ω - b‖ ^ 2 ∂ν) + ‖b‖ ^ 2 = _
  simp_rw [hn]
  rw [integral_add his hc, integral_sub he2 hi,
    integral_const_mul, integral_inner he b]
  simp [b, real_inner_self_eq_norm_sq]
  ring

/-- Integration and Young's inequality giving the constants in equation (46).
This applies to a conditional law after fixing the past as well as to an
unconditional probability measure. The pointwise bound is proved in
`noisy_acceleration_step`. -/
theorem expected_robust_step {a m H P : ℝ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hscale : a ^ 2 / m = H⁻¹) (z : E) (hz : m / 2 * ‖z‖ ^ 2 ≤ P)
    (e : Ω → E) (he : Integrable e ν)
    (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) ν)
    (next : Ω → ℝ) (hnext : Integrable next ν)
    (hstep : ∀ ω, next ω ≤ (1 - a) * P - a * ⟪z, e ω⟫_ℝ + ‖e ω‖ ^ 2 / H) :
    (∫ ω, next ω ∂ν) ≤ (1 - a / 2) * P +
      (∫ ω, ‖e ω - ∫ t, e t ∂ν‖ ^ 2 ∂ν) / H +
      (2 * a / m) * ‖∫ t, e t ∂ν‖ ^ 2 := by
  let b := ∫ t, e t ∂ν
  let V := ∫ ω, ‖e ω - b‖ ^ 2 ∂ν
  have hi := (he.const_inner z).const_mul a
  have hic : Integrable (fun _ : Ω => (1 - a) * P) ν := integrable_const _
  have his : Integrable (fun ω => (1 - a) * P - a * ⟪z, e ω⟫_ℝ) ν := hic.sub hi
  have hid : Integrable (fun ω => ‖e ω‖ ^ 2 / H) ν := he2.div_const H
  have hu : Integrable (fun ω => (1 - a) * P - a * ⟪z, e ω⟫_ℝ + ‖e ω‖ ^ 2 / H) ν :=
    ((integrable_const _).sub hi).add (he2.div_const H)
  have hi' := integral_mono hnext hu hstep
  rw [integral_add his hid,
    integral_sub hic hi, integral_const_mul a (fun ω => ⟪z, e ω⟫_ℝ),
    integral_inner (𝕜 := ℝ) he z, integral_div] at hi'
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi'
  have hmoment := second_moment_decomposition e he he2
  change V + ‖b‖ ^ 2 = _ at hmoment
  have hbase : H⁻¹ ≤ a / m := by
    rw [← hscale]
    exact div_le_div_of_nonneg_right (by nlinarith) hm.le
  have hcoef : ‖b‖ ^ 2 / H ≤ (a / m) * ‖b‖ ^ 2 := by
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hbase (sq_nonneg ‖b‖)
  have hb := bias_absorption hm ha z b hz
  change (∫ ω, next ω ∂ν) ≤ (1 - a / 2) * P + V / H + (2 * a / m) * ‖b‖ ^ 2
  change (∫ ω, next ω ∂ν) ≤ (1 - a) * P - a * ⟪z, b⟫_ℝ + _ at hi'
  rw [← hmoment, add_div] at hi'
  ring_nf at hb hcoef hi' ⊢
  linarith

omit [IsProbabilityMeasure ν] in
theorem markov_one_twelfth {X : Ω → ℝ} {B : ℝ} (hB : 0 < B)
    (hX : ∀ ω, 0 ≤ X ω) (hi : Integrable X ν) (hb : (∫ ω, X ω ∂ν) ≤ B) :
    ν.real {ω | 12 * B ≤ X ω} ≤ 1 / 12 := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hX) hi (12 * B)
  nlinarith

variable {F : Type*} [NormedAddCommGroup F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Theorem G.1's final 5/6 guarantee. `stopped` may be any output that agrees
with `raw` on paths whose original call count fits the integer budget N.
Existence and cost of the untruncated algorithm are not postulated here. -/
theorem fixed_budget_success (cost : Ω → ℕ) (raw stopped : Ω → E) (gradient : E → F)
    {N : ℕ} {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) (hN : 12 * B ≤ (N : ℝ))
    (hcost : Integrable (fun ω => (cost ω : ℝ)) ν)
    (hcostMean : (∫ ω, (cost ω : ℝ) ∂ν) ≤ B)
    (herror : Integrable (fun ω => ‖gradient (raw ω)‖ ^ 2) ν)
    (herrorMean : (∫ ω, ‖gradient (raw ω)‖ ^ 2 ∂ν) ≤ ε ^ 2 / 12)
    (hagree : ∀ ω, cost ω ≤ N → stopped ω = raw ω)
    (hbad : MeasurableSet {ω | ε < ‖gradient (stopped ω)‖}) :
    5 / 6 ≤ ν.real {ω | ‖gradient (stopped ω)‖ ≤ ε} := by
  have hc : ν.real {ω | 12 * B ≤ (cost ω : ℝ)} ≤ 1 / 12 :=
    markov_one_twelfth hB (fun ω => Nat.cast_nonneg _) hcost hcostMean
  have he : ν.real {ω | ε ^ 2 ≤ ‖gradient (raw ω)‖ ^ 2} ≤ 1 / 12 := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖gradient (raw ω)‖)) herror (ε ^ 2)
    nlinarith [sq_pos_of_pos hε]
  have hsub : {ω | ε < ‖gradient (stopped ω)‖} ⊆
      {ω | 12 * B ≤ (cost ω : ℝ)} ∪ {ω | ε ^ 2 ≤ ‖gradient (raw ω)‖ ^ 2} := by
    intro ω hw
    by_cases hc' : 12 * B ≤ (cost ω : ℝ)
    · exact Or.inl hc'
    · have hcn : cost ω ≤ N := by
        have : (cost ω : ℝ) ≤ N := (le_of_lt (lt_of_not_ge hc')).trans hN
        exact_mod_cast this
      have hsame := hagree ω hcn
      change ε < ‖gradient (stopped ω)‖ at hw
      rw [hsame] at hw
      right
      change ε ^ 2 ≤ ‖gradient (raw ω)‖ ^ 2
      nlinarith [norm_nonneg (gradient (raw ω))]
  have hbadBound : ν.real {ω | ε < ‖gradient (stopped ω)‖} ≤ 1 / 6 := by
    have hm := measureReal_mono (μ := ν) hsub
    have hu := measureReal_union_le (μ := ν)
      {ω | 12 * B ≤ (cost ω : ℝ)} {ω | ε ^ 2 ≤ ‖gradient (raw ω)‖ ^ 2}
    linarith
  have hcompl := measureReal_compl (μ := ν) hbad
  have heq : {ω | ε < ‖gradient (stopped ω)‖}ᶜ = {ω | ‖gradient (stopped ω)‖ ≤ ε} := by
    ext ω
    simp
  rw [heq, measureReal_univ_eq_one] at hcompl
  linarith

/-- Same-law outputs cannot succeed on two disjoint decision regions with
probability 2/3 each. This covers random zero-query outputs once disjointness
has actually been established for an admissible hard pair. -/
theorem disjoint_testing_obstruction (A B : Set Ω) (hB : MeasurableSet B) (hd : Disjoint A B) :
    ¬(2 / 3 ≤ ν.real A ∧ 2 / 3 ≤ ν.real B) := by
  have hu : ν.real (A ∪ B) = ν.real A + ν.real B := measureReal_union hd hB
  have hm : ν.real (A ∪ B) ≤ 1 := by
    simpa using measureReal_mono (μ := ν) (Set.subset_univ (A ∪ B))
  rintro ⟨ha, hb⟩
  linarith

end FreshGradientMinimax
