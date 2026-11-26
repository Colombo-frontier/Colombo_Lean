import FreshGradientMinimax.ProximalStability
import FreshGradientMinimax.Probability

/-! The outer descent analysis uses actual expectations of objective values,
proximal residuals, and max--min gaps. The hypotheses explicitly require
integrability and inner accuracy; construction and cost of the inner solver
are still separate obligations, not assumptions of any main complexity theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators
namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem expected_proximal_descent (c u : Ω → Euclid dx) (v : Ω → Euclid dy)
    (hc : Integrable (fun ω => O.value (c ω)) ν)
    (hu : Integrable (fun ω => O.value (u ω)) ν)
    (hw : Integrable (fun ω => ‖u ω - c ω‖ ^ 2) ν)
    (hr : Integrable (fun ω => ‖proximalResidual L (c ω) (O.proxPoint (c ω))‖ ^ 2) ν)
    (hg : Integrable (fun ω => (O.proximalObjective (c ω)).gap (u ω) (v ω)) ν) :
    (∫ ω, O.value (u ω) ∂ν) + L * (∫ ω, ‖u ω - c ω‖ ^ 2 ∂ν) ≤
      (∫ ω, O.value (c ω) ∂ν) -
        (∫ ω, ‖proximalResidual L (c ω) (O.proxPoint (c ω))‖ ^ 2 ∂ν) / (8 * L) +
        (∫ ω, (O.proximalObjective (c ω)).gap (u ω) (v ω) ∂ν) := by
  have h := integral_mono (hu.add (hw.const_mul L)) ((hc.sub (hr.div_const (8 * L))).add hg)
    (fun ω => O.proximal_gap_descent (c ω) (u ω) (v ω))
  simp only [Pi.add_apply, Pi.sub_apply] at h
  have his : Integrable (fun ω => O.value (c ω) -
      ‖proximalResidual L (c ω) (O.proxPoint (c ω))‖ ^ 2 / (8 * L)) ν := hc.sub (hr.div_const (8 * L))
  simpa only [integral_add hu (hw.const_mul L), integral_const_mul,
    integral_add his hg,
    integral_sub hc (hr.div_const (8 * L)), integral_div] using h

theorem expected_outer_telescope (T : ℕ) (x : ℕ → Ω → Euclid dx) (y : ℕ → Ω → Euclid dy)
    {Δ η : ℝ} (hΔ : O.PrimalGapAtMost Δ) (hstart : ∀ ω, x 0 ω = 0)
    (hv : ∀ t ≤ T, Integrable (fun ω => O.value (x t ω)) ν)
    (hw : ∀ t < T, Integrable (fun ω => ‖x (t + 1) ω - x t ω‖ ^ 2) ν)
    (hr : ∀ t < T, Integrable (fun ω => ‖proximalResidual L (x t ω) (O.proxPoint (x t ω))‖ ^ 2) ν)
    (hg : ∀ t < T, Integrable (fun ω => (O.proximalObjective (x t ω)).gap (x (t + 1) ω) (y (t + 1) ω)) ν)
    (haccuracy : ∀ t < T,
      (∫ ω, (O.proximalObjective (x t ω)).gap (x (t + 1) ω) (y (t + 1) ω) ∂ν) ≤ η) :
    (∑ t ∈ Finset.range T, ∫ ω, ‖proximalResidual L (x t ω) (O.proxPoint (x t ω))‖ ^ 2 ∂ν) / (8 * L) +
      L * (∑ t ∈ Finset.range T, ∫ ω, ‖x (t + 1) ω - x t ω‖ ^ 2 ∂ν) ≤ Δ + T * η := by
  apply sum_descent (f := fun t => ∫ ω, O.value (x t ω) ∂ν)
  · intro t ht
    have hs := O.expected_proximal_descent (x t) (x (t + 1)) (y (t + 1))
      (hv t (by omega)) (hv (t + 1) (by omega)) (hw t ht) (hr t ht) (hg t ht)
    have ha := haccuracy t ht
    linarith
  · have hi := integral_mono ((hv 0 (by omega)).sub (hv T le_rfl)) (integrable_const Δ)
      (fun ω => show O.value (x 0 ω) - O.value (x T ω) ≤ Δ by rw [hstart]; exact hΔ _)
    simp only [Pi.sub_apply] at hi
    simpa only [integral_sub (hv 0 (by omega)) (hv T le_rfl), integral_const,
      measureReal_univ_eq_one, smul_eq_mul, one_mul] using hi

omit [IsProbabilityMeasure ν] in
theorem expected_outer_residual_average {T : ℕ} (hT : 0 < T)
    (x : ℕ → Ω → Euclid dx) {Δ η : ℝ}
    (htel : (∑ t ∈ Finset.range T, ∫ ω, ‖proximalResidual L (x t ω) (O.proxPoint (x t ω))‖ ^ 2 ∂ν) / (8 * L) +
      L * (∑ t ∈ Finset.range T, ∫ ω, ‖x (t + 1) ω - x t ω‖ ^ 2 ∂ν) ≤ Δ + T * η) :
    (∑ t ∈ Finset.range T, ∫ ω, ‖proximalResidual L (x t ω) (O.proxPoint (x t ω))‖ ^ 2 ∂ν) / T ≤
      8 * L * (Δ / T + η) := by
  exact average_residual_bound hT O.L_pos
    (fun t _ => integral_nonneg (fun ω => sq_nonneg ‖x (t + 1) ω - x t ω‖)) htel

omit [IsProbabilityMeasure ν] in
theorem expected_outer_movement {T : ℕ} (x : ℕ → Ω → Euclid dx) {Δ η : ℝ}
    (htel : (∑ t ∈ Finset.range T, ∫ ω, ‖proximalResidual L (x t ω) (O.proxPoint (x t ω))‖ ^ 2 ∂ν) / (8 * L) +
      L * (∑ t ∈ Finset.range T, ∫ ω, ‖x (t + 1) ω - x t ω‖ ^ 2 ∂ν) ≤ Δ + T * η) :
    L * (∑ t ∈ Finset.range T, ∫ ω, ‖x (t + 1) ω - x t ω‖ ^ 2 ∂ν) ≤ Δ + T * η := by
  have hn : 0 ≤ (∑ t ∈ Finset.range T,
      ∫ ω, ‖proximalResidual L (x t ω) (O.proxPoint (x t ω))‖ ^ 2 ∂ν) / (8 * L) := by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    · have := O.L_pos; positivity
  linarith

omit [IsProbabilityMeasure ν] in
theorem expected_fine_gradient (c u : Ω → Euclid dx) (v : Ω → Euclid dy) {M η : ℝ}
    (hx : Integrable (fun ω => ‖gradient O.value (u ω)‖ ^ 2) ν)
    (hr : Integrable (fun ω => ‖proximalResidual L (c ω) (O.proxPoint (c ω))‖ ^ 2) ν)
    (hg : Integrable (fun ω => (O.proximalObjective (c ω)).gap (u ω) (v ω)) ν)
    (hm : (∫ ω, ‖proximalResidual L (c ω) (O.proxPoint (c ω))‖ ^ 2 ∂ν) ≤ M)
    (hη : (∫ ω, (O.proximalObjective (c ω)).gap (u ω) (v ω) ∂ν) ≤ η) :
    (∫ ω, ‖gradient O.value (u ω)‖ ^ 2 ∂ν) ≤ 2 * M + 144 * (L / μ) * L * η := by
  have hi := integral_mono hx ((hr.const_mul 2).add (hg.const_mul (144 * (L / μ) * L)))
    (fun ω => O.primal_gradient_from_saddle_gap (c ω) (u ω) (v ω))
  simp only [Pi.add_apply] at hi
  rw [integral_add (hr.const_mul 2) (hg.const_mul (144 * (L / μ) * L)),
    integral_const_mul, integral_const_mul] at hi
  have hcoef : 0 ≤ 144 * (L / μ) * L := by have := O.L_pos; have := O.μ_pos; positivity
  have hη' := mul_le_mul_of_nonneg_left hη hcoef
  linarith

end NCObjective
end FreshGradientMinimax
