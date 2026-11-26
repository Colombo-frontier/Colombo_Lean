import Nonsmooth.StrongScoreVariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem interval_weighted_mean_mem {a b : ℝ} (hab : a ≤ b) (w : ℝ → ℝ) (hw : Continuous w)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hZ : 0 < ∫ x in a..b, w x) :
    ((∫ x in a..b, x * w x) / (∫ x in a..b, w x)) ∈ Icc a b := by
  have hxf : Continuous (fun x : ℝ => x * w x) := continuous_id.mul hw
  have hlo : a * (∫ x in a..b, w x) ≤ ∫ x in a..b, x * w x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_const.mul hw).intervalIntegrable a b) (hxf.intervalIntegrable a b)
    intro x hx
    exact mul_le_mul_of_nonneg_right hx.1 (hw0 x hx)
  have hhi : (∫ x in a..b, x * w x) ≤ b * (∫ x in a..b, w x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      (hxf.intervalIntegrable a b) ((continuous_const.mul hw).intervalIntegrable a b)
    intro x hx
    exact mul_le_mul_of_nonneg_right hx.2 (hw0 x hx)
  exact ⟨(le_div_iff₀ hZ).mpr hlo, (div_le_iff₀ hZ).mpr hhi⟩

theorem interval_weighted_mean_centered {a b : ℝ} (w : ℝ → ℝ) (hw : Continuous w)
    (hZ : (∫ x in a..b, w x) ≠ 0) :
    (∫ x in a..b, (x - (∫ y in a..b, y * w y) / (∫ y in a..b, w y)) * w x) = 0 := by
  have hxf : Continuous (fun x : ℝ => x * w x) := continuous_id.mul hw
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (μ := (volume : Measure ℝ))
    (g := fun x : ℝ => ((∫ y in a..b, y * w y) / (∫ y in a..b, w y)) * w x)
    (hxf.intervalIntegrable a b)
    ((continuous_const.mul hw).intervalIntegrable a b), intervalIntegral.integral_const_mul]
  field_simp <;> ring

/-- A genuine normalized variance estimate: both the center and normalization are
computed from the given density, rather than postulated as extra assumptions. -/
theorem strong_score_interval_variance {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (w s : ℝ → ℝ) (hw : Continuous w) (hs : Continuous s)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hZ : 0 < ∫ x in a..b, w x)
    (hd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) :
    (∫ x in a..b, (x - (∫ y in a..b, y * w y) / (∫ y in a..b, w y)) ^ 2 * w x) /
      (∫ x in a..b, w x) ≤ ρ⁻¹ := by
  have hm := interval_weighted_mean_mem hab w hw hw0 hZ
  have h := strong_score_weighted_variance hab hm w s hw hs hw0 hd
    (fun x hx => monotone_adjusted_score s hmono hx hm)
    (interval_weighted_mean_centered w hw hZ.ne')
  apply (div_le_iff₀ hZ).mpr
  apply (mul_le_mul_iff_of_pos_left hρ).mp
  simpa only [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] using h

theorem convex_potential_interval_variance {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) :
    (∫ x in a..b, (x - (∫ y in a..b, y * Real.exp (-U y)) /
      (∫ y in a..b, Real.exp (-U y))) ^ 2 * Real.exp (-U x)) /
        (∫ x in a..b, Real.exp (-U x)) ≤ ρ⁻¹ := by
  have hw : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hZ : 0 < ∫ x in a..b, Real.exp (-U x) :=
    intervalIntegral.integral_pos hab hw.continuousOn (fun x _ => (Real.exp_pos _).le)
      ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩
  apply strong_score_interval_variance hab.le hρ (fun x => Real.exp (-U x)) s hw hs
    (fun x _ => (Real.exp_pos _).le) hZ ?_ hmono
  intro x hx
  convert! (hd x hx).neg.exp using 1 <;> (try simp only [Pi.neg_apply]) <;> ring

end
end Nonsmooth
