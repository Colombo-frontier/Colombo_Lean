import Nonsmooth.DerivativeEnergy
import Nonsmooth.ConvexPotentialTail
import Nonsmooth.SuperlevelCrossing

open MeasureTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A large value with derivative controlled by the curvature forces one
quantile tail to be bounded by twice the half-height superlevel mass. -/
theorem no_spike_positive_level_mass (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) {y : ℝ} (hy : 2 ≤ h y) :
    min (∫ x in Iic y, Real.exp (-U x)) (∫ x in Ioi y, Real.exp (-U x)) ≤
      2 * ∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x) := by
  have hh : Continuous h := continuous_iff_continuousAt.mpr (fun x => (hhd x).continuousAt)
  have hhalf : h y / 2 < h y := by linarith
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-U x) := (Real.exp_pos _).le
  have hmass : 0 ≤ ∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x) := integral_nonneg hw0
  by_cases hsign : 0 ≤ s y
  · apply (min_le_right _ _).trans
    rcases superlevel_first_crossing_right h hh hhalf with hall | ⟨b, hab, hb, hbetween⟩
    · have hle : (∫ x in Ioi y, Real.exp (-U x)) ≤
          ∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x) := by
        apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall hw0)
        exact Eventually.of_forall (fun x hx => (hall x hx.le).le)
      linarith
    · have he := derivative_energy_displacement hab.le h r s v hr hv
        (fun x _ => hhd x) (fun x _ => hsd x) (fun x _ => hcontrol x)
      rw [hb] at he
      have hsize : 1 ≤ (b - y) * s b := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) hsign]
      have ht := convex_potential_right_tail_le_twice_segment U s hs hd hmono hi hab hsign hsize
      have hle : (∫ x in y..b, Real.exp (-U x)) ≤
          ∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x) := by
        rw [intervalIntegral.integral_of_le hab.le]
        apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall hw0)
        apply Eventually.of_forall
        intro x hx
        rcases eq_or_lt_of_le hx.2 with heq | hlt
        · change h y / 2 ≤ h x
          rw [heq, hb]
        · exact (hbetween x ⟨hx.1, hlt⟩).le
      linarith
  · apply (min_le_left _ _).trans
    have hsign' : s y ≤ 0 := (lt_of_not_ge hsign).le
    rcases superlevel_first_crossing_left h hh hhalf with hall | ⟨a, hab, ha, hbetween⟩
    · have hle : (∫ x in Iic y, Real.exp (-U x)) ≤
          ∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x) := by
        apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall hw0)
        exact Eventually.of_forall (fun x hx => (hall x hx).le)
      linarith
    · have he := derivative_energy_displacement hab.le h r s v hr hv
        (fun x _ => hhd x) (fun x _ => hsd x) (fun x _ => hcontrol x)
      rw [ha] at he
      have hsize : 1 ≤ (y - a) * (-s a) := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab.le) hsign']
      have ht := convex_potential_left_tail_le_twice_segment U s hs hd hmono hi hab hsign' hsize
      have hle : (∫ x in a..y, Real.exp (-U x)) ≤
          ∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x) := by
        rw [intervalIntegral.integral_of_le hab.le]
        apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall hw0)
        apply Eventually.of_forall
        intro x hx
        rcases eq_or_lt_of_le hx.2 with heq | hlt
        · change h y / 2 ≤ h x
          simpa only [heq] using hhalf.le
        · exact (hbetween x ⟨hx.1, hlt⟩).le
      linarith

theorem no_spike_absolute_level_mass (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) {y : ℝ} (hy : 2 ≤ |h y|) :
    min (∫ x in Iic y, Real.exp (-U x)) (∫ x in Ioi y, Real.exp (-U x)) ≤
      2 * ∫ x in {x | |h y| / 2 ≤ |h x|}, Real.exp (-U x) := by
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-U x) := (Real.exp_pos _).le
  by_cases hsign : 0 ≤ h y
  · have hbound := no_spike_positive_level_mass U s v h r hs hv hr hd hsd hhd hmono hcontrol hi
      (by simpa only [abs_of_nonneg hsign] using hy)
    have hle : (∫ x in {x | h y / 2 ≤ h x}, Real.exp (-U x)) ≤
        ∫ x in {x | |h y| / 2 ≤ |h x|}, Real.exp (-U x) := by
      apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall hw0)
      exact Eventually.of_forall (fun x hx => by
        change |h y| / 2 ≤ |h x|
        rw [abs_of_nonneg hsign]
        exact hx.trans (le_abs_self _))
    linarith
  · have hsign' : h y < 0 := lt_of_not_ge hsign
    have hbound := no_spike_positive_level_mass U s v (fun x => -h x) (fun x => -r x)
      hs hv hr.neg hd hsd (fun x => (hhd x).neg) hmono
      (fun x => by simpa only [neg_sq] using hcontrol x) hi
      (by simpa only [abs_of_neg hsign'] using hy)
    have hle : (∫ x in {x | -h y / 2 ≤ -h x}, Real.exp (-U x)) ≤
        ∫ x in {x | |h y| / 2 ≤ |h x|}, Real.exp (-U x) := by
      apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall hw0)
      exact Eventually.of_forall (fun x hx => by
        change |h y| / 2 ≤ |h x|
        rw [abs_of_neg hsign']
        exact hx.trans (neg_le_abs _))
    linarith

end
end Nonsmooth
