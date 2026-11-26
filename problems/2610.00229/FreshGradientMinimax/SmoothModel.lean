import FreshGradientMinimax.Probability
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Connection of the F.2 recurrence to an actual differentiable objective.
The displayed lower and upper Taylor inequalities use the convention m/2,H/2.
These are assumptions on the objective, not assumptions of an optimizer or a
complexity conclusion. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure SmoothStrongModel (Q : E → ℝ) (grad : E → E) (m H : ℝ) : Prop where
  derivative : ∀ x, HasFDerivAt Q (innerSL ℝ (grad x)) x
  lower : ∀ x y, Q x + ⟪grad x, y - x⟫_ℝ + m / 2 * ‖y - x‖ ^ 2 ≤ Q y
  upper : ∀ x y, Q y ≤ Q x + ⟪grad x, y - x⟫_ℝ + H / 2 * ‖y - x‖ ^ 2

theorem acceleration_parameter {m H : ℝ} (hm : 0 < m) (hmH : m ≤ H) :
    0 ≤ Real.sqrt (m / H) ∧ Real.sqrt (m / H) ≤ 1 ∧
      (Real.sqrt (m / H)) ^ 2 / m = H⁻¹ := by
  have hH : 0 < H := hm.trans_le hmH
  refine ⟨Real.sqrt_nonneg _, ?_, ?_⟩
  · apply (Real.sqrt_le_one).mpr
    exact (div_le_one hH).mpr hmH
  · rw [Real.sq_sqrt (div_nonneg hm.le hH.le)]
    field_simp
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Lemma F.2 with the algorithmic updates substituted into the conclusion.
The distribution of e may be continuous. The same result applies to each
conditional distribution fixing the past; the filtration construction itself
is outside this theorem. -/
theorem robust_acceleration {Q : E → ℝ} {grad : E → E} {a m H : ℝ}
    (model : SmoothStrongModel Q grad m H)
    (hm : 0 < m) (hH : 0 < H) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hscale : a ^ 2 / m = H⁻¹) (v x z : E) (hmin : ∀ t, Q v ≤ Q t)
    (e : Ω → E) (he : Integrable e ν) (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) ν)
    (hnext : Integrable (fun ω => acceleratedPotential Q m v
      (acceleratedY a x z - H⁻¹ • (grad (acceleratedY a x z) + e ω))
      (acceleratedZ a m z (acceleratedY a x z) (grad (acceleratedY a x z) + e ω))) ν) :
    (∫ ω, acceleratedPotential Q m v
      (acceleratedY a x z - H⁻¹ • (grad (acceleratedY a x z) + e ω))
      (acceleratedZ a m z (acceleratedY a x z) (grad (acceleratedY a x z) + e ω)) ∂ν) ≤
      (1 - a / 2) * acceleratedPotential Q m v x z +
        (∫ ω, ‖e ω - ∫ t, e t ∂ν‖ ^ 2 ∂ν) / H +
        (2 * a / m) * ‖∫ t, e t ∂ν‖ ^ 2 := by
  let y := acceleratedY a x z
  let d := grad y
  have hxy : x - y = -a • (z - y) := acceleratedY_relation (by positivity) x z
  have hconv : Q y + ⟪d, x - y⟫_ℝ ≤ Q x := by
    have h := model.lower y x
    have hn : 0 ≤ m / 2 * ‖x - y‖ ^ 2 := by positivity
    change Q y + ⟪d, x - y⟫_ℝ + m / 2 * ‖x - y‖ ^ 2 ≤ Q x at h
    linarith
  have hstrong : Q y - Q v + m / 2 * ‖y - v‖ ^ 2 ≤ ⟪d, y - v⟫_ℝ := by
    have h := model.lower y v
    have hi : v - y = -(y - v) := by abel
    rw [hi, inner_neg_right, norm_neg] at h
    change Q y + -⟪d, y - v⟫_ℝ + m / 2 * ‖y - v‖ ^ 2 ≤ Q v at h
    linarith
  have hsmooth (err : E) := model.upper y (y - H⁻¹ • (d + err))
  have hex := exact_acceleration_inequality hm ha ha1 hscale v x y z d hxy hconv hstrong
  have hP : 0 ≤ acceleratedPotential Q m v x z := by
    unfold acceleratedPotential
    have h := hmin x
    have hn : 0 ≤ m / 2 * ‖z - v‖ ^ 2 := by positivity
    linarith
  have hdescent : 0 ≤ Q y - Q v - ‖d‖ ^ 2 / (2 * H) := by
    have h := noisy_primal_step hH y d 0 (hsmooth 0)
    simp only [add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero] at h
    have hmin' := hmin (y - H⁻¹ • d)
    linarith
  have hz := exact_z_distance ha v x y z d hP hdescent hex
  exact expected_robust_step hm ha ha1 hscale _ hz e he he2 _ hnext
    (fun ω => noisy_acceleration_step hm hH ha ha1 hscale v x y z d (e ω)
      hxy hconv hstrong (hsmooth (e ω)))

end FreshGradientMinimax
