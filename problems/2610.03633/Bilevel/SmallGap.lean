import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Septic cutoff core and small-gap certificates

This module proves the polynomial derivative, its sharp bound on `[0,1]`,
monotonicity and range of the core, and the range of the clipped step. It also
proves local two-sign separation and the quadratic gap sandwich from explicit
core-value/minimizer hypotheses. It does not claim global C³ gluing, the global
stationary-set separation, or the two-hypothesis statistical lower bound.
-/

namespace Bilevel.SmallGap

noncomputable section

/-- Polynomial core of the septic step in article lines 963–969. -/
def septicCore (t : ℝ) : ℝ := 35 * t ^ 4 - 84 * t ^ 5 + 70 * t ^ 6 - 20 * t ^ 7

/-- The globally clipped step, without yet asserting its C³ gluing. -/
def septicStep (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 1 else septicCore t

theorem septicCore_hasDerivAt (t : ℝ) :
    HasDerivAt septicCore (140 * t ^ 3 * (1 - t) ^ 3) t := by
  unfold septicCore
  convert (((((hasDerivAt_id t).pow 4).const_mul 35).sub
    (((hasDerivAt_id t).pow 5).const_mul 84)).add
    (((hasDerivAt_id t).pow 6).const_mul 70)).sub
    (((hasDerivAt_id t).pow 7).const_mul 20) using 1
  dsimp
  ring

theorem septicCore_deriv (t : ℝ) : deriv septicCore t = 140 * t ^ 3 * (1 - t) ^ 3 :=
  (septicCore_hasDerivAt t).deriv

theorem septicCore_deriv_bounds (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ deriv septicCore t ∧ deriv septicCore t ≤ 35 / 16 := by
  rw [septicCore_deriv]
  have hp : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hupper : t * (1 - t) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hc := pow_le_pow_left₀ hp hupper 3
  constructor
  · have ht0 := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    positivity
  · nlinarith

/-- The derivative bound is attained at the midpoint. -/
theorem septicCore_deriv_midpoint : deriv septicCore (1 / 2) = 35 / 16 := by
  rw [septicCore_deriv]
  norm_num

theorem septicCore_monotoneOn : MonotoneOn septicCore (Set.Icc (0 : ℝ) 1) := by
  have hd : Differentiable ℝ septicCore := fun t => (septicCore_hasDerivAt t).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd.continuous.continuousOn
    hd.differentiableOn
  intro t ht
  exact (septicCore_deriv_bounds t (interior_subset ht)).1

theorem septicCore_range (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ septicCore t ∧ septicCore t ≤ 1 := by
  have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have ho : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hlo := septicCore_monotoneOn hz ht ht.1
  have hhi := septicCore_monotoneOn ht ho ht.2
  have hzero : septicCore 0 = 0 := by norm_num [septicCore]
  have hone : septicCore 1 = 1 := by norm_num [septicCore]
  rw [hzero] at hlo
  rw [hone] at hhi
  exact ⟨hlo, hhi⟩

theorem septicStep_range (t : ℝ) : 0 ≤ septicStep t ∧ septicStep t ≤ 1 := by
  unfold septicStep
  split_ifs with hzero hone
  · norm_num
  · norm_num
  · exact septicCore_range t ⟨le_of_not_ge hzero, le_of_not_ge hone⟩

/-- The clipped step has the stated derivative inside its transition interval. -/
theorem septicStep_hasDerivAt_interior (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt septicStep (140 * t ^ 3 * (1 - t) ^ 3) t := by
  apply (septicCore_hasDerivAt t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with u hu0 hu1
  simp only [septicStep, if_neg (not_le.mpr hu0), if_neg (not_le.mpr hu1)]

/-- A real scalar cannot be close to both opposite shifts at once. This is the
local-core separation argument in article line 1124, not its global extension. -/
theorem opposite_shift_separation (a γ : ℝ) (hγ : 0 ≤ γ) :
    2 * γ ≤ |a - γ| + |a + γ| := by
  have h := abs_sub (a + γ) (a - γ)
  have heq : a + γ - (a - γ) = 2 * γ := by ring
  rw [heq, abs_of_nonneg (by positivity : 0 ≤ 2 * γ)] at h
  linarith

/-- Completion of the scalar quadratic, for any linear coefficient. -/
theorem quadratic_complete_square (Γ a x : ℝ) (hΓ : Γ ≠ 0) :
    Γ / 2 * x ^ 2 - a * x = Γ / 2 * (x - a / Γ) ^ 2 - a ^ 2 / (2 * Γ) := by
  field_simp
  ring

theorem quadratic_lower_bound (Γ a x : ℝ) (hΓ : 0 < Γ) :
    -(a ^ 2 / (2 * Γ)) ≤ Γ / 2 * x ^ 2 - a * x := by
  rw [quadratic_complete_square Γ a x hΓ.ne']
  have hpos : 0 ≤ Γ / 2 * (x - a / Γ) ^ 2 := by positivity
  linarith

/-- The small-gap sandwich given explicit values in the core and a genuine
global minimizer. Membership in the core and the profile estimates must be
established independently for the paper's full functions. -/
theorem gap_sandwich (F P : ℝ → ℝ) (Γ L γ ω xstar : ℝ)
    (hΓ : 0 < Γ) (hL : 0 ≤ L) (hω : ω ^ 2 = 1)
    (hzero : F 0 = 0)
    (hmin : ∀ x, F xstar ≤ F x)
    (hcore_min : F xstar = Γ / 2 * xstar ^ 2 - ω * γ * xstar + P xstar)
    (hP_min : 0 ≤ P xstar)
    (hcore_test : F (ω * γ / (Γ + L)) =
      Γ / 2 * (ω * γ / (Γ + L)) ^ 2 - ω * γ * (ω * γ / (Γ + L)) +
        P (ω * γ / (Γ + L)))
    (hP_test : P (ω * γ / (Γ + L)) ≤ L / 2 * (ω * γ / (Γ + L)) ^ 2) :
    γ ^ 2 / (2 * (Γ + L)) ≤ F 0 - F xstar ∧
      F 0 - F xstar ≤ γ ^ 2 / (2 * Γ) := by
  have hsum : 0 < Γ + L := by linarith
  have hωγ : (ω * γ) ^ 2 = γ ^ 2 := by rw [mul_pow, hω, one_mul]
  have hq := quadratic_lower_bound Γ (ω * γ) xstar hΓ
  rw [hωγ] at hq
  have htest : Γ / 2 * (ω * γ / (Γ + L)) ^ 2 -
      ω * γ * (ω * γ / (Γ + L)) + L / 2 * (ω * γ / (Γ + L)) ^ 2 =
        -(γ ^ 2 / (2 * (Γ + L))) := by
    calc
      _ = -((ω * γ) ^ 2 / (2 * (Γ + L))) := by field_simp; ring
      _ = _ := by rw [hωγ]
  have htest_bound : F (ω * γ / (Γ + L)) ≤ -(γ ^ 2 / (2 * (Γ + L))) := by
    rw [hcore_test]
    linarith
  constructor
  · rw [hzero]
    linarith [hmin (ω * γ / (Γ + L))]
  · rw [hzero, hcore_min]
    linarith

end
end Bilevel.SmallGap
