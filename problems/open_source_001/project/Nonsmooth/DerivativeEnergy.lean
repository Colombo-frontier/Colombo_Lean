import Nonsmooth.StrongScoreVariance
import Nonsmooth.ArcEnergy

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Pointwise derivative control integrates to a squared displacement bound.
This is the finite-interval estimate used by the no-spike argument. -/
theorem derivative_energy_displacement {a b : ℝ} (hab : a ≤ b)
    (h r s v : ℝ → ℝ) (hr : Continuous r) (hv : Continuous v)
    (hd : ∀ x ∈ Icc a b, HasDerivAt h (r x) x)
    (hsd : ∀ x ∈ Icc a b, HasDerivAt s (v x) x)
    (hcontrol : ∀ x ∈ Icc a b, (r x) ^ 2 ≤ v x) :
    (h b - h a) ^ 2 ≤ (b - a) * (s b - s a) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) (hr.intervalIntegrable a b)
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hsd x (by simpa only [uIcc_of_le hab] using hx)) (hv.intervalIntegrable a b)
  have hle : (∫ x in a..b, (r x) ^ 2) ≤ ∫ x in a..b, v x :=
    intervalIntegral.integral_mono_on hab ((hr.pow 2).intervalIntegrable a b)
      (hv.intervalIntegrable a b) hcontrol
  have hsq := interval_integral_square_le hlt hr
  rw [hh] at hsq
  rw [← hs]
  exact hsq.trans (mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hab))

end
end Nonsmooth
