import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A short numerical estimate sufficient for the odd-sphere argument, proved using
the derivative of sin(t)-t*cos(t) and the half-angle formula at pi/12. -/
theorem pi_square_le_twenty_one_halves : Real.pi ^ 2 ≤ 21 / 2 := by
  let g : ℝ → ℝ := fun t => Real.sin t - t * Real.cos t
  have hd (t : ℝ) : HasDerivAt g (t * Real.sin t) t := by
    convert! (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1 <;>
      simp [id_eq]
  have hc : Continuous g := Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)
  have hm : MonotoneOn g (Set.Icc 0 (Real.pi / 12)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    exact mul_nonneg ht'.1 (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (by linarith [ht'.2, Real.pi_pos]))
  have hp : (0 : ℝ) ≤ Real.pi / 12 := by positivity
  have hg := hm (Set.left_mem_Icc.mpr hp) (Set.right_mem_Icc.mpr hp) hp
  have hpc : Real.pi * Real.cos (Real.pi / 12) ≤ 12 * Real.sin (Real.pi / 12) := by
    simp only [g, Real.sin_zero, zero_mul, sub_zero] at hg
    linarith
  have hcospos : 0 ≤ Real.cos (Real.pi / 12) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsquare := pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le hcospos) hpc 2
  rw [mul_pow, mul_pow] at hsquare
  have hangle : 2 * (Real.pi / 12) = Real.pi / 6 := by ring
  have hcos : Real.cos (Real.pi / 12) ^ 2 = (2 + Real.sqrt 3) / 4 := by
    have h := Real.cos_two_mul (Real.pi / 12)
    rw [hangle, Real.cos_pi_div_six] at h
    linarith
  have hsin : Real.sin (Real.pi / 12) ^ 2 = (2 - Real.sqrt 3) / 4 := by
    have h := Real.sin_sq_add_cos_sq (Real.pi / 12)
    rw [hcos] at h
    linarith
  rw [hcos, hsin] at hsquare
  have hsqrt : (173 : ℝ) / 100 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hprod := mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hsqrt)
  nlinarith

end
end Nonsmooth
