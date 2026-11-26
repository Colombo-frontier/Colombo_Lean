import NCConcave16991.ConePrimitives
import Mathlib.Analysis.Normed.Group.Bounded

/-! # A fixed universal bound for the concrete density derivative

The bound is constructed from the actual derivative on a compact interval;
outside that interval the derivative is identically zero.
-/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives Set
open scoped ContDiff Topology

theorem density_deriv_zero_left {t : ℝ} (ht : t ≤ 0) : deriv density t = 0 := by
  have hh : HasDerivAt density 0 t := by
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (by linarith : t < 1 / 4)] with s hs
    exact density_zero_left hs.le
  exact hh.deriv

theorem density_deriv_zero_right {t : ℝ} (ht : 1 ≤ t) : deriv density t = 0 := by
  have hh : HasDerivAt density 0 t := by
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (by linarith : (7 / 8 : ℝ) < t)] with s hs
    exact density_zero_right hs.le
  exact hh.deriv

theorem density_derivative_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv density t| ≤ C := by
  have hd : ContDiff ℝ ∞ (deriv density) := (contDiff_infty_iff_deriv.mp density_contDiff).2
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hd.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have htC : |deriv density t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t ht
    exact htC.trans (le_max_left _ _)
  · have hout : t ≤ 0 ∨ 1 ≤ t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      exact ht.imp le_of_lt le_of_lt
    rcases hout with hl | hr
    · rw [density_deriv_zero_left hl, abs_zero]
      exact le_max_right _ _
    · rw [density_deriv_zero_right hr, abs_zero]
      exact le_max_right _ _

def densitySlopeBound : ℝ := Classical.choose density_derivative_bounded

theorem densitySlopeBound_nonneg : 0 ≤ densitySlopeBound :=
  (Classical.choose_spec density_derivative_bounded).1

theorem density_deriv_bound (t : ℝ) : |deriv density t| ≤ densitySlopeBound :=
  (Classical.choose_spec density_derivative_bounded).2 t

theorem latch_second_derivative_bound (t : ℝ) :
    |deriv (deriv latch) t| ≤ 16 * densitySlopeBound := by
  have hfun : deriv latch = fun s ↦ 4 * density (4 * s - 1) :=
    funext (fun s ↦ (latch_hasDerivAt s).deriv)
  have hd := ((density_contDiff.differentiable (by simp) (4 * t - 1)).hasDerivAt.comp t
    (((hasDerivAt_id t).const_mul 4).sub_const 1)).const_mul 4
  change HasDerivAt (fun s ↦ 4 * density (4 * s - 1))
    (4 * (deriv density (4 * t - 1) * (4 * 1))) t at hd
  rw [hfun, hd.deriv]
  norm_num only [mul_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  nlinarith [density_deriv_bound (4 * t - 1)]

theorem exitStep_second_derivative_bound (t : ℝ) :
    |deriv (deriv exitStep) t| ≤ densitySlopeBound := by
  have hfun : deriv exitStep = fun s ↦ density (s - 1) :=
    funext (fun s ↦ (exitStep_hasDerivAt s).deriv)
  have hd := (density_contDiff.differentiable (by simp) (t - 1)).hasDerivAt.comp t
    ((hasDerivAt_id t).sub_const 1)
  change HasDerivAt (fun s ↦ density (s - 1)) (deriv density (t - 1) * 1) t at hd
  rw [hfun, hd.deriv]
  simpa only [mul_one] using density_deriv_bound (t - 1)

end NCConcave16991.ConeSmooth
