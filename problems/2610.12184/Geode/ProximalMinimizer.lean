import Geode.GeodesicConvex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-! Existence and localization of actual proximal minimizers for globally
Lipschitz objectives on the finite-dimensional hyperboloid. -/
namespace Geode.Lorentz

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_of_lipschitz_bound {f : Point E → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) : Continuous f := by
  have h : LipschitzWith ⟨L, hL⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_mk] using hlip x y
  exact h.continuous

theorem proximal_distance_bound {f : Point E → ℝ} {L a : ℝ}
    (hL : 0 ≤ L) (ha : 0 < a) (hlip : ∀ x y, |f x - f y| ≤ L * dist x y)
    (x p : Point E)
    (hmin : ∀ y, f p + a * dist p x ^ 2 ≤ f y + a * dist y x ^ 2) :
    dist p x ≤ L / a := by
  have h := hmin x
  simp only [dist_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at h
  have hl := (le_abs_self (f x - f p)).trans (hlip x p)
  rw [dist_comm x p] at hl
  have hmul : a * dist p x ^ 2 ≤ L * dist p x := by linarith
  by_cases hd : dist p x = 0
  · rw [hd]
    exact div_nonneg hL ha.le
  · have hdpos : 0 < dist p x := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    apply (le_div_iff₀ ha).mpr
    have hh : (a * dist p x) * dist p x ≤ L * dist p x := by nlinarith only [hmul]
    have := (mul_le_mul_right hdpos).mp hh
    nlinarith only [this]

variable [FiniteDimensional ℝ E]

theorem proximal_minimizer_exists {f : Point E → ℝ} {L a : ℝ}
    (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) (x : Point E) :
    ∃ p : Point E, ∀ y, f p + a * dist p x ^ 2 ≤ f y + a * dist y x ^ 2 := by
  have hf := continuous_of_lipschitz_bound hL hlip
  let F : Point E → ℝ := fun y => f y + a * dist y x ^ 2
  have hF : Continuous F := hf.add (continuous_const.mul ((continuous_id.dist continuous_const).pow 2))
  have hx : x ∈ Metric.closedBall x (L + 1) := Metric.mem_closedBall_self (by linarith)
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedBall x (L + 1)).exists_isMinOn ⟨x, hx⟩ hF.continuousOn
  refine ⟨p, ?_⟩
  intro y
  change F p ≤ F y
  by_cases hy : y ∈ Metric.closedBall x (L + 1)
  · exact hmin hy
  · have hd : L + 1 < dist y x := lt_of_not_ge (fun h => hy h)
    have hd0 : 0 < dist y x := by linarith
    have hfx := (le_abs_self (f x - f y)).trans (hlip x y)
    rw [dist_comm x y] at hfx
    have hq := mul_le_mul_of_nonneg_right ha (sq_nonneg (dist y x))
    have hpx : F p ≤ F x := hmin hx
    have hp' : F p ≤ f x := by simpa only [F, dist_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hpx
    have hout : f x ≤ F y := by
      change f x ≤ f y + a * dist y x ^ 2
      nlinarith [mul_pos hd0 (show 0 < dist y x - L by linarith)]
    exact hp'.trans hout

end Geode.Lorentz
