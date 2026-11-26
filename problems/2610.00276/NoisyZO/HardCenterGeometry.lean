import NoisyZO.HardAdmissibility
import NoisyZO.SmoothCutoff
import NoisyZO.HardHypercube
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Automatic smoothness and center geometry for the radial hard family

These are the parts of the hard-family admissibility certificate that follow
directly from the explicit smooth cutoff and its flat inner ball.  They need
not be supplied as quantitative derivative assumptions.
-/

open Metric Filter
open scoped ContDiff Gradient Topology

namespace NoisyZO

noncomputable section

/-- The explicit radial hard value is smooth to every finite or infinite
order. -/
theorem hardValue_radialCutoff_contDiff
    {d : ℕ} (c h : ℝ) (hh : 0 < h) (s : Fin d → ℝ) {n : ℕ∞} :
    ContDiff ℝ n
      (hardValue (radialCutoff d h hh) c s) := by
  unfold hardValue
  apply (contDiff_norm_sq ℝ).sub
  apply (contDiff_const.mul ?_).mul (radialCutoff_contDiff d h hh)
  unfold signedSum
  fun_prop

/-- The normalized Boolean center has norm exactly half the perturbation
coefficient, independently of dimension. -/
theorem norm_hardCenter_hypercubeSign
    {d : ℕ} (hd : 0 < d) (c : ℝ) (s : Hypercube d) :
    ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ = |c| / 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt_sq : (Real.sqrt d) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt hdR.le
  have hsqrt_ne : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdR).ne'
  have hsq := norm_hardCenter_sq_of_signs
    (c / Real.sqrt d) (hypercubeSign s) (hypercubeSign_sq s)
  have hsq' :
      ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ ^ 2 = c ^ 2 / 4 := by
    rw [hsq, div_pow, hsqrt_sq]
    field_simp [show (d : ℝ) ≠ 0 from hdR.ne']
  have habs_sq : (|c| / 2) ^ 2 = c ^ 2 / 4 := by
    rw [div_pow, sq_abs]
    norm_num
  have hnorm0 : 0 ≤ ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ :=
    norm_nonneg _
  have habs0 : 0 ≤ |c| / 2 := by positivity
  nlinarith

/-- A center strictly inside the cutoff's flat inner ball is a stationary
point of the explicit radial hard value. -/
theorem hardValue_radialCutoff_center_stationary
    {d : ℕ} (h ρ : ℝ) (hh : 0 < h) (s : Fin d → ℝ)
    (hcenter : ‖hardCenter ρ s‖ < h / 2) :
    ∇ (hardValue (radialCutoff d h hh) ρ s) (hardCenter ρ s) = 0 := by
  let xstar : Point d := hardCenter ρ s
  let completed : Point d → ℝ :=
    fun x ↦ ‖x - xstar‖ ^ 2 - ‖xstar‖ ^ 2
  have hball : ball (0 : Point d) (h / 2) ∈ 𝓝 xstar := by
    apply Metric.isOpen_ball.mem_nhds
    simpa [Metric.mem_ball, dist_zero_right, xstar] using hcenter
  have heq :
      hardValue (radialCutoff d h hh) ρ s =ᶠ[𝓝 xstar] completed := by
    filter_upwards [hball] with x hx
    apply hardValue_eq_completedSquare
    apply radialCutoff_eq_one_of_norm_le_half d h hh
    have hx' : ‖x‖ < h / 2 := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    exact hx'.le
  have hmin : IsMinOn completed Set.univ xstar := by
    rw [isMinOn_iff]
    intro x _hx
    dsimp only [completed]
    simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub]
    nlinarith [sq_nonneg ‖x - xstar‖]
  have hlocal : IsLocalMin
      (hardValue (radialCutoff d h hh) ρ s) xstar :=
    (hmin.isLocalMin Filter.univ_mem).congr heq.symm
  have hfderiv := hlocal.fderiv_eq_zero
  unfold gradient
  rw [hfderiv, map_zero]

/-- For the manuscript's saturated bandwidth and amplitude range, the hard
center lies in the unit ball and strictly inside the flat cutoff region. -/
theorem rateHardCenter_geometry
    {d : ℕ} (hd : 0 < d) (β a h : ℝ)
    (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hh : 0 < h) (hh1 : h ≤ 1) (s : Hypercube d) :
    let c := a * h ^ (β - 1)
    ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ ≤ 1 ∧
      ‖hardCenter (c / Real.sqrt d) (hypercubeSign s)‖ < h / 2 := by
  dsimp only
  rw [norm_hardCenter_hypercubeSign hd]
  have hexp : 1 ≤ β - 1 := by linarith
  have hpow_pos : 0 < h ^ (β - 1) := Real.rpow_pos_of_pos hh _
  have hpow_le : h ^ (β - 1) ≤ h :=
    Real.rpow_le_self_of_le_one hh.le hh1 hexp
  have hc0 : 0 ≤ a * h ^ (β - 1) := mul_nonneg ha.le hpow_pos.le
  rw [abs_of_nonneg hc0]
  constructor
  · nlinarith
  · have : a * h ^ (β - 1) ≤ h / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hpow_le ha.le]
    linarith

end

end NoisyZO
