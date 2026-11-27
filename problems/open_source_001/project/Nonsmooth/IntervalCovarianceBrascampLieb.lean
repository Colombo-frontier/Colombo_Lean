import Nonsmooth.SteinPenalty
import Nonsmooth.IntervalPotentialEvents

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem convex_potential_stein_solution (U s f : ℝ → ℝ)
    (hs : Continuous s) (hf : Continuous f) (hd : ∀ x, HasDerivAt U (s x) x)
    (a b : ℝ) (hmean : (∫ x in a..b, f x * Real.exp (-U x)) = 0) :
    ∃ g q : ℝ → ℝ, Continuous g ∧ Continuous q ∧
      (∀ x, HasDerivAt g (q x) x) ∧ (∀ x, q x = f x + s x * g x) ∧ g a = 0 ∧ g b = 0 := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let w := fun x => Real.exp (-U x)
  have hw : Continuous w := Real.continuous_exp.comp hU.neg
  let H := fun x => ∫ t in a..x, f t * w t
  have hHd (x : ℝ) : HasDerivAt H (f x * w x) x :=
    intervalIntegral.integral_hasDerivAt_right ((hf.mul hw).intervalIntegrable a x)
      (hf.mul hw).aestronglyMeasurable.stronglyMeasurableAtFilter (hf.mul hw).continuousAt
  let g := fun x => H x * Real.exp (U x)
  let q := fun x => f x + s x * g x
  have hg : Continuous g :=
    (continuous_iff_continuousAt.mpr (fun x => (hHd x).continuousAt)).mul (Real.continuous_exp.comp hU)
  have hq : Continuous q := hf.add (hs.mul hg)
  refine ⟨g, q, hg, hq, ?_, fun _ => rfl, ?_, ?_⟩
  · intro x
    have hcancel : Real.exp (-U x) * Real.exp (U x) = 1 := by rw [← Real.exp_add]; simp
    convert! (hHd x).mul (hd x).exp using 1
    dsimp only [q, g, w]
    rw [mul_assoc (f x), hcancel]
    ring
  · simp only [g, H, intervalIntegral.integral_same, zero_mul]
  · change (∫ x in a..b, f x * Real.exp (-U x)) * Real.exp (U b) = 0
    rw [hmean, zero_mul]

theorem centered_interval_covariance_brascamp_lieb {a b ρ : ℝ} (hab : a < b) (hρ : 0 ≤ ρ)
    (U s v f f' : ℝ → ℝ) (hs : Continuous s) (hv : Continuous v)
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt U (s x) x)
    (hsd : ∀ x ∈ Icc a b, HasDerivAt s (v x) x)
    (hfd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hvρ : ∀ x ∈ Icc a b, 0 < v x - ρ)
    (hmean : (∫ x in a..b, f x * Real.exp (-U x)) = 0) :
    (∫ x, (f x) ^ 2 ∂intervalDensityLaw (fun x => Real.exp (-U x)) a b) +
      ρ * (∫ x, x * f x ∂intervalDensityLaw (fun x => Real.exp (-U x)) a b) ^ 2 ≤
      ∫ x, (f' x) ^ 2 / (v x - ρ) ∂intervalDensityLaw (fun x => Real.exp (-U x)) a b := by
  obtain ⟨g, q, hg, hq, hgd, hrel, ha, hb⟩ := convex_potential_stein_solution U s f hs hf hd a b hmean
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let w := fun x => Real.exp (-U x)
  have hw : Continuous w := Real.continuous_exp.comp hU.neg
  have hw0 (x : ℝ) : 0 ≤ w x := (Real.exp_pos _).le
  have hZ : 0 < ∫ x in a..b, w x := intervalIntegral.integral_pos hab hw.continuousOn
    (fun x _ => hw0 x) ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩
  have hwd (x : ℝ) : HasDerivAt w (-s x * w x) x := by
    convert! (hd x).neg.exp using 1
    dsimp only [w, Pi.neg_apply]
    ring
  have henergy := weighted_stein_gradient_with_penalty hab.le w s v f f' g q hw hv hf hf' hg hq
    (fun x _ => hw0 x) hvρ (fun x _ => hwd x) hsd hfd (fun x _ => hgd x) (fun x _ => hrel x) ha hb
  have hmoment := weighted_stein_first_moment hab.le w s f g q hw hf hg
    (fun x _ => hwd x) (fun x _ => hgd x) (fun x _ => hrel x) ha hb
  let Q := intervalDensityLaw w a b
  letI : IsProbabilityMeasure Q := intervalDensityLaw_probability hab.le w hw hw0 hZ
  have hg2 : MemLp g 2 Q :=
    (memLp_two_iff_integrable_sq hg.measurable.aestronglyMeasurable).mpr
      (intervalDensityLaw_integrable_continuous hab.le w hw hw0 hZ (fun x => (g x) ^ 2) (hg.pow 2))
  have hJ : (∫ x, g x ∂Q) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂Q := by
    have hn := variance_nonneg g Q
    rw [variance_eq_sub hg2] at hn
    simp only [Pi.pow_apply] at hn
    linarith
  have hM : (∫ x, x * f x ∂Q) = -(∫ x, g x ∂Q) := by
    rw [show Q = intervalDensityLaw w a b from rfl,
      intervalDensityLaw_integral hab.le w hw hw0 (fun x => x * f x),
      intervalDensityLaw_integral hab.le w hw hw0 g, hmoment, neg_div]
  have hE : (∫ x, (f x) ^ 2 ∂Q) + ρ * (∫ x, (g x) ^ 2 ∂Q) ≤
      ∫ x, (f' x) ^ 2 / (v x - ρ) ∂Q := by
    rw [show Q = intervalDensityLaw w a b from rfl,
      intervalDensityLaw_integral hab.le w hw hw0 (fun x => (f x) ^ 2),
      intervalDensityLaw_integral hab.le w hw hw0 (fun x => (g x) ^ 2),
      intervalDensityLaw_integral hab.le w hw hw0 (fun x => (f' x) ^ 2 / (v x - ρ))]
    simpa only [add_div, mul_div_assoc] using div_le_div_of_nonneg_right henergy hZ.le
  change (∫ x, (f x) ^ 2 ∂Q) + ρ * (∫ x, x * f x ∂Q) ^ 2 ≤ _
  rw [hM, neg_sq]
  nlinarith [mul_le_mul_of_nonneg_left hJ hρ]

/-- Strengthened Brascamp--Lieb: the left side includes the squared covariance
of the coordinate with the test function. -/
theorem interval_covariance_brascamp_lieb {a b ρ : ℝ} (hab : a < b) (hρ : 0 ≤ ρ)
    (U s v f f' : ℝ → ℝ) (hs : Continuous s) (hv : Continuous v)
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt U (s x) x)
    (hsd : ∀ x ∈ Icc a b, HasDerivAt s (v x) x)
    (hfd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hvρ : ∀ x ∈ Icc a b, 0 < v x - ρ) :
    let Q := intervalDensityLaw (fun x => Real.exp (-U x)) a b
    variance f Q + ρ * (∫ x, x * (f x - ∫ y, f y ∂Q) ∂Q) ^ 2 ≤
      ∫ x, (f' x) ^ 2 / (v x - ρ) ∂Q := by
  dsimp only
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let w := fun x => Real.exp (-U x)
  have hw : Continuous w := Real.continuous_exp.comp hU.neg
  have hw0 (x : ℝ) : 0 ≤ w x := (Real.exp_pos _).le
  have hZ : 0 < ∫ x in a..b, w x := intervalIntegral.integral_pos hab hw.continuousOn
    (fun x _ => hw0 x) ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩
  let m := ∫ x, f x ∂intervalDensityLaw w a b
  have hm : m = (∫ x in a..b, f x * w x) / (∫ x in a..b, w x) :=
    intervalDensityLaw_integral hab.le w hw hw0 f
  have hcenter : (∫ x in a..b, (f x - m) * Real.exp (-U x)) = 0 := by
    change (∫ x in a..b, (f x - m) * w x) = 0
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => f x * w x) (g := fun x : ℝ => m * w x)
      ((hf.mul hw).intervalIntegrable a b)
      ((continuous_const.mul hw).intervalIntegrable a b), intervalIntegral.integral_const_mul, hm]
    field_simp [hZ.ne'] <;> ring
  have he := centered_interval_covariance_brascamp_lieb hab hρ U s v (fun x => f x - m) f'
    hs hv (hf.sub continuous_const) hf' hd hsd (fun x hx => (hfd x hx).sub_const m) hvρ hcenter
  rw [variance_eq_integral hf.measurable.aemeasurable]
  exact he

end
end Nonsmooth
