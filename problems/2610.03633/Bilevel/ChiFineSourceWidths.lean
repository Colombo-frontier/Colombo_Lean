import Bilevel.ChiFineCouplingCore

/-! The actual normal schedule has a geometric width sum. This is the
source-force improvement: arbitrary normal arguments cost the largest
normal width, not the whole frontier amplitude. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiFine
open ZeroChainSchedule

theorem normal_width_half_step (c β θ : ℝ) (hc : 0≤c) (hβ : 0≤β) (hθ : 1≤θ)
    (j : ℕ) (hj : j<levels θ) : 2*width c β θ (j+1)≤width c β θ j := by
  have hθpos : 0<θ := by linarith
  have hden : 0<(4:ℝ)^(j+1) := by positivity
  have hrat : 1≤Real.log θ/(4:ℝ)^(j+1) := (one_le_div hden).mpr (four_power_le_log θ j hj)
  have heq : bExponent (j+1)-bExponent j=3/(2*(4:ℝ)^(j+1)) := by
    dsimp [bExponent]
    rw [pow_succ]
    field_simp
    ring
  have hgap : 1≤Real.log θ*(bExponent (j+1)-bExponent j) := by
    rw [heq]
    have he : Real.log θ*(3/(2*(4:ℝ)^(j+1)))=(3/2:ℝ)*(Real.log θ/(4:ℝ)^(j+1)) := by ring
    rw [he]
    linarith
  have hexp := Real.exp_le_exp.mpr
    (show Real.log θ*(-bExponent (j+1))+1≤Real.log θ*(-bExponent j) by nlinarith)
  rw [Real.exp_add] at hexp
  have he1 : 2≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hmul := mul_le_mul_of_nonneg_left he1 (Real.exp_pos (Real.log θ*(-bExponent (j+1)))).le
  have hh : 2*Real.exp (Real.log θ*(-bExponent (j+1)))≤Real.exp (Real.log θ*(-bExponent j)) := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hh (mul_nonneg hc hβ)
  dsimp [width]
  rw [Real.rpow_def_of_pos hθpos,Real.rpow_def_of_pos hθpos]
  nlinarith

theorem normal_width_sum (c β θ : ℝ) (hc : 0≤c) (hβ : 0≤β) (hθ : 1≤θ) :
    (∑ j ∈ Finset.range (levels θ+1),width c β θ j)≤2*width c β θ 0 := by
  have hsum (N : ℕ) (hN : N≤levels θ) :
      (∑ j ∈ Finset.range (N+1),width c β θ j)≤2*width c β θ 0-width c β θ N := by
    induction N with
    | zero => simp only [Nat.zero_add,Finset.sum_range_one];linarith
    | succ N ih =>
      have hh := normal_width_half_step c β θ hc hβ hθ N (by omega)
      have hp := ih (by omega)
      rw [Finset.sum_range_succ]
      linarith
  have hn : 0≤width c β θ (levels θ) := by
    dsimp [width]
    exact mul_nonneg (mul_nonneg hc hβ) (Real.rpow_nonneg (by linarith) _)
  linarith [hsum (levels θ) le_rfl]

end Bilevel.ChiFine
