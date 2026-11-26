import Nonsmooth.IntervalPotentialMGF
import Nonsmooth.EventComplement

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem intervalDensityLaw_integrable_continuous {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hZ : 0 < ∫ x in a..b, w x) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (intervalDensityLaw w a b) := by
  have hb : Integrable f (intervalDensityMeasure w a b) := by
    rw [intervalDensityMeasure, integrable_withDensity_iff hw.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hw0 _)]
    exact (hf.mul hw).continuousOn.integrableOn_Icc
  have hm : intervalDensityMeasure w a b univ ≠ 0 := by
    rw [intervalDensityMeasure_mass hab w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  simpa only [intervalDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
    hb.smul_measure (ENNReal.inv_ne_top.mpr hm)

theorem interval_potential_centered_exp_integrable (U : ℝ → ℝ) (hU : Continuous U)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    let Q := intervalDensityLaw (fun x => Real.exp (-U x)) a b
    Integrable (fun x => Real.exp (t * (x - ∫ y : ℝ, y ∂Q))) Q := by
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hZ : 0 < ∫ x in a..b, Real.exp (-U x) :=
    intervalIntegral.integral_pos hab hwc.continuousOn (fun x _ => (Real.exp_pos _).le)
      ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩
  apply intervalDensityLaw_integrable_continuous hab.le _ hwc (fun x => (Real.exp_pos _).le) hZ
  fun_prop

theorem interval_potential_event_mean_two_sided (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) {A : Set ℝ} (hAm : MeasurableSet A)
    (hA : intervalDensityLaw (fun x => Real.exp (-U x)) a b A ≠ 0)
    (hAc : intervalDensityLaw (fun x => Real.exp (-U x)) a b Aᶜ ≠ 0) :
    let Q := intervalDensityLaw (fun x => Real.exp (-U x)) a b
    (∫ x, (x - ∫ y : ℝ, y ∂Q) ∂Q[|A]) ^ 2 ≤
      min (2 * ρ⁻¹ * Real.log (1 / Q.real A))
        ((Q.real Aᶜ / Q.real A) ^ 2 * (2 * ρ⁻¹ * Real.log (1 / Q.real Aᶜ))) := by
  let Q := intervalDensityLaw (fun x => Real.exp (-U x)) a b
  let V := fun x : ℝ => x - ∫ y : ℝ, y ∂Q
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw0 : ∀ x, 0 ≤ Real.exp (-U x) := fun x => (Real.exp_pos _).le
  have hZ : 0 < ∫ x in a..b, Real.exp (-U x) :=
    intervalIntegral.integral_pos hab hwc.continuousOn (fun x _ => hw0 x)
      ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩
  letI := intervalDensityLaw_probability hab.le _ hwc hw0 hZ
  have hi : Integrable (fun x : ℝ => x) Q :=
    (intervalDensityLaw_memLp_two hab.le _ hwc hw0 hZ).integrable (by norm_num)
  have hV : Integrable V Q := hi.sub (integrable_const _)
  have hmean : (∫ x, V x ∂Q) = 0 := by
    change (∫ x : ℝ, x - ∫ y : ℝ, y ∂Q ∂Q) = 0
    rw [integral_sub hi (integrable_const _)]
    simp
  have hInt (u : ℝ) : Integrable (fun x => Real.exp ⟪u, V x⟫_ℝ) Q := by
    simpa [RCLike.inner_apply', Q, V, mul_comm] using interval_potential_centered_exp_integrable U hU hab u
  have hMGF (u : ℝ) : (∫ x, Real.exp ⟪u, V x⟫_ℝ ∂Q) ≤ 1 * Real.exp (ρ⁻¹ * ‖u‖ ^ 2 / 2) := by
    have ha : u ^ 2 / (2 * ρ) = ρ⁻¹ * ‖u‖ ^ 2 / 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      ring
    have h := interval_potential_centered_mgf U s hU hs hab hρ hd hmono u
    try dsimp only at h
    rw [ha] at h
    simpa [RCLike.inner_apply', Q, V, mul_comm] using h
  have h := event_barycenter_two_sided hV hmean (inv_pos.mpr hρ)
    (by norm_num : (0 : ℝ) < 1) hInt hMGF hAm hA hAc
  simpa only [Real.norm_eq_abs, sq_abs] using h

end
end Nonsmooth
