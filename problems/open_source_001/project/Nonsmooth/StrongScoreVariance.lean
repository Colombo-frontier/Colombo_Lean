import Nonsmooth.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- One-dimensional integration by parts: a strongly increasing negative logarithmic
derivative controls the centered second moment, with the interval boundary retained. -/
theorem strong_score_weighted_variance {a b m ρ : ℝ} (hab : a ≤ b) (hm : m ∈ Icc a b)
    (w s : ℝ → ℝ) (hw : Continuous w) (hs : Continuous s)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hscore : ∀ x ∈ Icc a b, ρ * (x - m) ^ 2 ≤ (x - m) * (s x - s m))
    (hmean : (∫ x in a..b, (x - m) * w x) = 0) :
    ρ * (∫ x in a..b, (x - m) ^ 2 * w x) ≤ ∫ x in a..b, w x := by
  have hcw : Continuous (fun x : ℝ => (x - m) * w x) := by fun_prop
  have hsw : Continuous (fun x : ℝ => (x - m) * s x * w x) := by fun_prop
  have hsq : Continuous (fun x : ℝ => (x - m) ^ 2 * w x) := by fun_prop
  have hds : Continuous (fun x : ℝ => (x - m) * (s x - s m) * w x) := by fun_prop
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y : ℝ => (y - m) * w y) (w x - (x - m) * s x * w x) x := by
    convert! ((hasDerivAt_id x).sub_const m).mul (hd x hx) using 1 <;>
      (try simp only [id_eq]) <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa only [uIcc_of_le hab] using hx))
    ((hw.sub hsw).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hw.intervalIntegrable a b) (hsw.intervalIntegrable a b)] at he
  have hbd : 0 ≤ (b - m) * w b - (a - m) * w a := by
    have hright := mul_nonneg (sub_nonneg.mpr hm.2) (hw0 b ⟨hab, le_rfl⟩)
    have hleft := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm.1) (hw0 a ⟨le_rfl, hab⟩)
    linarith
  have hupper : (∫ x in a..b, (x - m) * s x * w x) ≤ ∫ x in a..b, w x := by linarith
  have hcancel : (∫ x in a..b, (x - m) * (s x - s m) * w x) =
      ∫ x in a..b, (x - m) * s x * w x := by
    have hf : (fun x : ℝ => (x - m) * (s x - s m) * w x) =
        fun x => (x - m) * s x * w x - s m * ((x - m) * w x) := by
      funext x; ring
    rw [hf]
    have hsub := intervalIntegral.integral_sub (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => (x - m) * s x * w x)
      (g := fun x : ℝ => s m * ((x - m) * w x)) (hsw.intervalIntegrable a b)
      ((continuous_const.mul hcw).intervalIntegrable a b)
    rw [intervalIntegral.integral_const_mul, hmean, mul_zero, sub_zero] at hsub
    convert! hsub using 1
  have hlower : ρ * (∫ x in a..b, (x - m) ^ 2 * w x) ≤
      ∫ x in a..b, (x - m) * (s x - s m) * w x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_const.mul hsq).intervalIntegrable a b) (hds.intervalIntegrable a b)
    intro x hx
    simpa only [mul_assoc, Pi.mul_apply] using mul_le_mul_of_nonneg_right (hscore x hx) (hw0 x hx)
  exact hlower.trans (hcancel ▸ hupper)

theorem monotone_adjusted_score {a b ρ : ℝ} (s : ℝ → ℝ)
    (hs : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) {x m : ℝ}
    (hx : x ∈ Icc a b) (hm : m ∈ Icc a b) :
    ρ * (x - m) ^ 2 ≤ (x - m) * (s x - s m) := by
  rcases le_total m x with h | h
  · have he := hs hm hx h
    have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr he)
    try dsimp only at hp
    nlinarith
  · have he := hs hx hm h
    have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr he)
    try dsimp only at hp
    nlinarith

/-- For a density exp(-U), monotonicity of U'(x)-ρx gives the sharp inverse-curvature
variance estimate on every finite interval once centered at its actual mean. -/
theorem convex_potential_weighted_variance {a b m ρ : ℝ} (hab : a ≤ b) (hm : m ∈ Icc a b)
    (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b))
    (hmean : (∫ x in a..b, (x - m) * Real.exp (-U x)) = 0) :
    ρ * (∫ x in a..b, (x - m) ^ 2 * Real.exp (-U x)) ≤ ∫ x in a..b, Real.exp (-U x) := by
  apply strong_score_weighted_variance hab hm (fun x => Real.exp (-U x)) s
    (Real.continuous_exp.comp hU.neg) hs
    (fun x _ => (Real.exp_pos _).le) ?_ ?_ hmean
  · intro x hx
    convert! (hd x hx).neg.exp using 1 <;>
      (try simp only [Pi.neg_apply]) <;> ring
  · intro x hx
    exact monotone_adjusted_score s hmono hx hm

end
end Nonsmooth
