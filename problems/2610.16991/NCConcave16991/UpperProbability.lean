import NCConcave16991.UpperRecurrence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

open MeasureTheory

namespace NCConcave16991

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Actual Markov conversion for an integrable nonnegative random residual square.
This is the probability step at the end of Appendix B. -/
theorem markov_squared_residual {r : Ω → ℝ} (hr : Measurable r)
    (hrnonneg : ∀ ω, 0 ≤ r ω) (hrint : Integrable (fun ω => r ω ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε)
    (hmean : (∫ ω, r ω ^ 2 ∂μ) < ε ^ 2 / 200) :
    μ.real {ω | ε ≤ r ω} < 1 / 200 := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (r ω))) hrint (ε ^ 2)
  have hsets : {ω | ε ^ 2 ≤ r ω ^ 2} = {ω | ε ≤ r ω} := by
    ext ω
    change (ε ^ 2 ≤ r ω ^ 2) ↔ ε ≤ r ω
    exact sq_le_sq₀ hε.le (hrnonneg ω)
  rw [hsets] at hmark
  have hep : 0 < ε ^ 2 := sq_pos_of_pos hε
  nlinarith

/-- Mean squared residual below eps²/200 gives actual success probability >199/200. -/
theorem stationarity_success_probability {r : Ω → ℝ} (hr : Measurable r)
    (hrnonneg : ∀ ω, 0 ≤ r ω) (hrint : Integrable (fun ω => r ω ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε)
    (hmean : (∫ ω, r ω ^ 2 ∂μ) < ε ^ 2 / 200) :
    (199 / 200 : ℝ) < μ.real {ω | r ω < ε} := by
  have hfail := markov_squared_residual μ hr hrnonneg hrint hε hmean
  have hm : MeasurableSet {ω | ε ≤ r ω} := measurableSet_le measurable_const hr
  have hc := measureReal_compl (μ := μ) hm
  have hsets : {ω | ε ≤ r ω}ᶜ = {ω | r ω < ε} := by ext ω; simp
  rw [hsets, probReal_univ] at hc
  linarith

/-- In particular Appendix B's numerical guarantee is stronger than 2/3. -/
theorem stationarity_two_thirds {r : Ω → ℝ} (hr : Measurable r)
    (hrnonneg : ∀ ω, 0 ≤ r ω) (hrint : Integrable (fun ω => r ω ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε)
    (hmean : (∫ ω, r ω ^ 2 ∂μ) < ε ^ 2 / 200) :
    (2 / 3 : ℝ) ≤ μ.real {ω | r ω < ε} := by
  have h := stationarity_success_probability μ hr hrnonneg hrint hε hmean
  linarith

/-- The same actual measure guarantee stated for a normed-space random gradient. -/
theorem gradient_stationarity_probability {H : Type*} [NormedAddCommGroup H]
    [MeasurableSpace H] [BorelSpace H] {g : Ω → H} (hg : Measurable g)
    (hgint : Integrable (fun ω => ‖g ω‖ ^ 2) μ) {ε : ℝ} (hε : 0 < ε)
    (hmean : (∫ ω, ‖g ω‖ ^ 2 ∂μ) < ε ^ 2 / 200) :
    (199 / 200 : ℝ) < μ.real {ω | ‖g ω‖ < ε} :=
  stationarity_success_probability μ hg.norm (fun ω => norm_nonneg _) hgint hε hmean

/-- Combining two genuine bad events uses measure subadditivity, as in Appendix C. -/
theorem combined_failure_budget (abort badOutput : Set Ω)
    (ha : μ.real abort ≤ 1 / 12) (ho : μ.real badOutput ≤ 1 / 6) :
    μ.real (abort ∪ badOutput) ≤ 1 / 4 := by
  have hu := measureReal_union_le (μ := μ) abort badOutput
  linarith

end NCConcave16991


namespace NCConcave16991

open scoped BigOperators

/-- The expectation of an actual independent uniform output index is its finite mean. -/
theorem uniform_output_mean_square {ι H : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [NormedAddCommGroup H]
    (g : ι → H) :
    (∫ i, ‖g i‖ ^ 2 ∂(PMF.uniformOfFintype ι).toMeasure) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖g i‖ ^ 2 := by
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, smul_eq_mul, ← Finset.mul_sum]

/-- A deterministic finite-mean certificate gives the claimed probability for an
actual uniform output distribution, with no expectation or probability oracle. -/
theorem uniform_output_stationarity {ι H : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [NormedAddCommGroup H]
    [MeasurableSpace H] [BorelSpace H] (g : ι → H) {ε : ℝ} (hε : 0 < ε)
    (hmean : (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖g i‖ ^ 2 < ε ^ 2 / 200) :
    (199 / 200 : ℝ) < (PMF.uniformOfFintype ι).toMeasure.real {i | ‖g i‖ < ε} := by
  apply gradient_stationarity_probability (PMF.uniformOfFintype ι).toMeasure
    (measurable_of_countable g) Integrable.of_finite hε
  rw [uniform_output_mean_square]
  exact hmean

end NCConcave16991


namespace NCConcave16991

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- General Markov form, also covering Appendix C's eps²/6 threshold. -/
theorem markov_mean_square_bound {r : Ω → ℝ}
    (hrnonneg : ∀ ω, 0 ≤ r ω) (hrint : Integrable (fun ω => r ω ^ 2) μ)
    {ε q : ℝ} (hε : 0 < ε)
    (hmean : (∫ ω, r ω ^ 2 ∂μ) ≤ q * ε ^ 2) :
    μ.real {ω | ε ≤ r ω} ≤ q := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (r ω))) hrint (ε ^ 2)
  have hsets : {ω | ε ^ 2 ≤ r ω ^ 2} = {ω | ε ≤ r ω} := by
    ext ω
    change (ε ^ 2 ≤ r ω ^ 2) ↔ ε ≤ r ω
    exact sq_le_sq₀ hε.le (hrnonneg ω)
  rw [hsets] at hm
  have hep : 0 < ε ^ 2 := sq_pos_of_pos hε
  nlinarith

open scoped BigOperators

/-- The same uniform-output expectation, indexed by the outer trajectory's range. -/
theorem uniform_trajectory_mean_square {H : Type*} [NormedAddCommGroup H]
    {S : ℕ} [NeZero S] [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)]
    (g : ℕ → H) :
    (∫ i : Fin S, ‖g i‖ ^ 2 ∂(PMF.uniformOfFintype (Fin S)).toMeasure) =
      (∑ k ∈ Finset.range S, ‖g k‖ ^ 2) / S := by
  rw [uniform_output_mean_square]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖g k‖ ^ 2)]
  ring

end NCConcave16991



namespace NCConcave16991

/-- Complete deterministic-trajectory certificate for Appendix C's actual uniform
output: the local inexact proximal inequalities imply failure probability ≤1/6. -/
theorem inexact_proximal_uniform_failure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (x p : ℕ → E) {L Δ lower ε : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) {S : ℕ} [NeZero S]
    [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)]
    (hclose : ∀ k, ‖x (k + 1) - p k‖ ^ 2 ≤ 2 * (ε ^ 2 / (288 * L)) / L)
    (hstep : ∀ k, L * ‖x (k + 1) - x k‖ ^ 2 ≤
      F (x k) - F (x (k + 1)) + ε ^ 2 / (288 * L))
    (hlower : lower ≤ F (x S)) (hgap : F (x 0) - lower ≤ Δ)
    (hS : 96 * (L * Δ / ε ^ 2) ≤ (S : ℝ)) :
    (PMF.uniformOfFintype (Fin S)).toMeasure.real
      {i | ε ≤ ‖(2 * L) • (x i - p i)‖} ≤ 1 / 6 := by
  have hSp : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  have hd := inexact_proximal_outer_descent F x p hL hSp hclose hstep hlower hgap
  have hp := accelerated_parameter_stationarity hL hΔ hε hS hSp
  apply markov_mean_square_bound (PMF.uniformOfFintype (Fin S)).toMeasure
    (fun i => norm_nonneg ((2 * L) • (x i - p i))) Integrable.of_finite hε
  rw [uniform_trajectory_mean_square (fun k => (2 * L) • (x k - p k))]
  nlinarith

end NCConcave16991


