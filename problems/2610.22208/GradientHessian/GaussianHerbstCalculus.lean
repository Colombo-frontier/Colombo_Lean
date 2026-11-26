import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The scalar differential-inequality step in the Herbst argument. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Filter Set
open scoped Topology

theorem herbst_calculus {H H' : ℝ → ℝ} {c : ℝ}
    (hd : ∀ t, HasDerivAt H (H' t) t) (hzero : H 0 = 0)
    (hbound : ∀ t, 0 < t → t * H' t - H t ≤ c * t ^ 2)
    {t : ℝ} (ht : 0 < t) : H t ≤ t * H' 0 + c * t ^ 2 := by
  let K : ℝ → ℝ := fun s => H s / s - c * s
  let K' : ℝ → ℝ := fun s => (s * H' s - H s) / s ^ 2 - c
  have hk (s : ℝ) (hs : 0 < s) : HasDerivAt K (K' s) s := by
    convert ((hd s).div (hasDerivAt_id s) hs.ne').sub
      ((hasDerivAt_id s).const_mul c) using 1
    dsimp [K, K']
    ring
  have hm : AntitoneOn K (Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    · intro s hs
      exact (hk s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hk s (by simpa only [interior_Ioi, mem_Ioi] using hs)).hasDerivWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
      have hq := (div_le_iff₀ (sq_pos_of_pos hs')).mpr (hbound s hs')
      dsimp [K']
      linarith
  have hslope : Tendsto (fun s => H s / s) (𝓝[>] (0 : ℝ)) (𝓝 (H' 0)) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (hd 0).tendsto_slope_zero_right
  have hlin : Tendsto (fun s : ℝ => c * s) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using hid.const_mul c
  have hlim : Tendsto K (𝓝[>] 0) (𝓝 (H' 0)) := by
    simpa only [sub_zero] using hslope.sub hlin
  have hle : K t ≤ H' 0 := by
    apply ge_of_tendsto hlim
    have hlt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t :=
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with s hs hst
    exact hm hs ht hst.le
  have hdiv : H t / t ≤ H' 0 + c * t := by dsimp [K] at hle; linarith
  have h := (div_le_iff₀ ht).mp hdiv
  nlinarith only [h]

end GradientHessian.GaussianConcentration
