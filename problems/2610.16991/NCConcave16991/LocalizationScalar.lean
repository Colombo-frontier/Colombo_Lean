import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual scalar cutoff and integral radial profile from Appendix E

`Real.smoothTransition` is the paper's explicit exponential step, including
its smooth gluing at 0 and 1. The radial profile below is its actual integral,
not a bundle of assumed derivative bounds. Its restriction to nonnegative
radii is the radial length used in the source; we prove the identity region,
the constant outer region, value bounds, and the exact derivative.
-/

namespace NCConcave16991.LocalizationScalar

open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def gate (t : ℝ) : ℝ := Real.smoothTransition ((5 * t - 1) / 4)

theorem gate_contDiff : ContDiff ℝ ∞ gate := by
  unfold gate
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem gate_nonneg (t : ℝ) : 0 ≤ gate t := Real.smoothTransition.nonneg _
theorem gate_le_one (t : ℝ) : gate t ≤ 1 := Real.smoothTransition.le_one _

theorem gate_zero {t : ℝ} (ht : t ≤ 1 / 5) : gate t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem gate_one {t : ℝ} (ht : 1 ≤ t) : gate t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- Exact inactive first jet, including the transition boundary. -/
theorem gate_hasDerivAt_zero {t : ℝ} (ht : t ≤ 1 / 5) : HasDerivAt gate 0 t := by
  have hmin : IsLocalMin gate t := by
    apply IsMinOn.isLocalMin (s := univ)
    · intro s _
      rw [gate_zero ht]
      exact gate_nonneg s
    · exact Filter.univ_mem
  have hd := (gate_contDiff.differentiable (by simp) t).hasDerivAt
  simpa only [hmin.deriv_eq_zero] using hd

theorem gate_hasDerivAt_one {t : ℝ} (ht : 1 ≤ t) : HasDerivAt gate 0 t := by
  have hmax : IsLocalMax gate t := by
    apply IsMaxOn.isLocalMax (s := univ)
    · intro s _
      rw [gate_one ht]
      exact gate_le_one s
    · exact Filter.univ_mem
  have hd := (gate_contDiff.differentiable (by simp) t).hasDerivAt
  simpa only [hmax.deriv_eq_zero] using hd

/-- Radial speed: one in the identity region and zero beyond twice the cap. -/
noncomputable def radialSpeed (C r : ℝ) : ℝ :=
  1 - Real.smoothTransition ((r - C) / C)

theorem radialSpeed_contDiff (C : ℝ) : ContDiff ℝ ∞ (radialSpeed C) := by
  unfold radialSpeed
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem radialSpeed_nonneg (C r : ℝ) : 0 ≤ radialSpeed C r :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem radialSpeed_le_one (C r : ℝ) : radialSpeed C r ≤ 1 := by
  unfold radialSpeed
  linarith [Real.smoothTransition.nonneg ((r - C) / C)]

theorem radialSpeed_one {C r : ℝ} (hC : 0 < C) (hr : r ≤ C) :
    radialSpeed C r = 1 := by
  unfold radialSpeed
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hC.le)]
  ring

theorem radialSpeed_zero {C r : ℝ} (hC : 0 < C) (hr : 2 * C ≤ r) :
    radialSpeed C r = 0 := by
  unfold radialSpeed
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hC).mpr (by linarith))]
  ring

noncomputable def radialLength (C r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, radialSpeed C s

theorem radialLength_hasDerivAt (C r : ℝ) :
    HasDerivAt (radialLength C) (radialSpeed C r) r := by
  have hc := (radialSpeed_contDiff C).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem radialLength_deriv (C : ℝ) : deriv (radialLength C) = radialSpeed C := by
  funext r
  exact (radialLength_hasDerivAt C r).deriv

theorem radialLength_contDiff (C : ℝ) : ContDiff ℝ ∞ (radialLength C) := by
  rw [contDiff_infty_iff_deriv, radialLength_deriv]
  exact ⟨fun r => (radialLength_hasDerivAt C r).differentiableAt, radialSpeed_contDiff C⟩

theorem radialLength_identity {C r : ℝ} (hC : 0 < C) (hr : r ≤ C) :
    radialLength C r = r := by
  unfold radialLength
  have he : (∫ s in (0 : ℝ)..r, radialSpeed C s) = ∫ _ in (0 : ℝ)..r, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact radialSpeed_one hC (hs.2.trans (max_le hC.le hr))
  rw [he]
  simp

theorem radialLength_nonneg {C r : ℝ} (hr : 0 ≤ r) : 0 ≤ radialLength C r :=
  intervalIntegral.integral_nonneg_of_forall hr (radialSpeed_nonneg C)

theorem radialLength_le_radius {C r : ℝ} (hr : 0 ≤ r) : radialLength C r ≤ r := by
  have hc := (radialSpeed_contDiff C).continuous
  have hh := intervalIntegral.integral_mono (μ := volume) hr (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (radialSpeed_le_one C)
  simpa [radialLength] using hh

theorem radialLength_constant {C r : ℝ} (hC : 0 < C) (hr : 2 * C ≤ r) :
    radialLength C r = radialLength C (2 * C) := by
  have hc := (radialSpeed_contDiff C).continuous
  have hz : (∫ s in (2 * C)..r, radialSpeed C s) = 0 := by
    calc
      _ = ∫ _ in (2 * C)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hr] at hs
        exact radialSpeed_zero hC hs.1
      _ = 0 := by simp
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (2 * C)) (hc.intervalIntegrable (2 * C) r)
  simpa only [hz, add_zero, radialLength] using hh.symm

theorem radialLength_le_cap {C r : ℝ} (hC : 0 < C) (hr : 0 ≤ r) :
    radialLength C r ≤ 2 * C := by
  by_cases hrc : r ≤ 2 * C
  · exact (radialLength_le_radius hr).trans hrc
  · rw [radialLength_constant hC (le_of_not_ge hrc)]
    exact radialLength_le_radius (by positivity)

theorem radialLength_ge_cap {C r : ℝ} (hC : 0 < C) (hr : C ≤ r) :
    C ≤ radialLength C r := by
  have hc := (radialSpeed_contDiff C).continuous
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 C) (hc.intervalIntegrable C r)
  have hpos := intervalIntegral.integral_nonneg_of_forall (μ := volume) hr (radialSpeed_nonneg C)
  have hid := radialLength_identity hC (le_refl C)
  change (∫ s in (0 : ℝ)..C, radialSpeed C s) = C at hid
  change C ≤ ∫ s in (0 : ℝ)..r, radialSpeed C s
  linarith

end NCConcave16991.LocalizationScalar
