import GradientHessian.RadialSquash
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Dimension-free geometry for the manuscript's physical register gradient.
All radial maps and derivatives below are the actual smooth squash. -/

noncomputable section
namespace GradientHessian.LatchGeometry

open Filter
open scoped Topology InnerProductSpace
open RadialSquash

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem squash_fderiv_identity {K : ℝ} (hK : 0 < K) (z : E) (hz : ‖z‖ < K) :
    fderiv ℝ (squash K) z = ContinuousLinearMap.id ℝ E := by
  have he : squash K =ᶠ[𝓝 z] (id : E → E) := by
    have hn : ∀ᶠ x : E in 𝓝 z, ‖x‖ < K :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds hz)
    filter_upwards [hn] with x hx
    exact squash_identity hK hx.le
  rw [he.fderiv_eq, fderiv_id]

theorem squash_fderiv_symmetric {K : ℝ} (hK : 0 < K) (z v w : E) :
    ⟪fderiv ℝ (squash K) z v, w⟫_ℝ = ⟪v, fderiv ℝ (squash K) z w⟫_ℝ := by
  by_cases hz : z = 0
  · subst z
    rw [squash_fderiv_identity hK _ (by simpa using hK)]
    simp
  · rw [squash_fderiv_apply hK hz, squash_fderiv_apply hK hz]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v z]
    ring

theorem readout_hasGradientAt [CompleteSpace E] {K : ℝ} (hK : 0 < K) (v z : E) :
    HasGradientAt (fun x => ⟪v, squash K x⟫_ℝ) (fderiv ℝ (squash K) z v) z := by
  have hR := (squash_contDiff hK).differentiable (by norm_num) z
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (innerSL ℝ v).hasFDerivAt.comp z hR.hasFDerivAt using 1
  ext w
  simp only [InnerProductSpace.toDual_apply, ContinuousLinearMap.comp_apply, innerSL_apply]
  exact squash_fderiv_symmetric hK z v w

/-- An outward residual with positive bounded readout lies inside the identity
ball whenever its norm is at most one. This is the radial step used twice in
the source register proof. -/
theorem positive_readout_force_inside (v z : E) (hv : ‖v‖ = 1) {c : ℝ}
    (hc : 0 ≤ c) (hu0 : 0 < ⟪v, squash 8 z⟫_ℝ)
    (hu1 : ⟪v, squash 8 z⟫_ℝ < 1)
    (hf : ‖(8 : ℝ) • z - c • fderiv ℝ (squash 8) z v‖ ≤ 1) : ‖z‖ < 8 := by
  by_contra hlarge
  have hr : (8 : ℝ) ≤ ‖z‖ := le_of_not_gt hlarge
  have hz : z ≠ 0 := by intro he; norm_num [he] at hr
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let s := scale 8 ‖z‖
  let b := ⟪v, z⟫_ℝ
  let w := z - b • v
  let t := (IntegralProfiles.density 1 (‖z‖ / 8) - s) * b / ‖z‖ ^ 2
  let beta := 8 - c * t
  have hs := scale_bounds (by norm_num : (0 : ℝ) < 8) hr0
  have hread : ⟪v, squash 8 z⟫_ℝ = s * b := by simp [s, b, squash, real_inner_smul_right]
  have hb : 0 < b := by nlinarith only [hu0, hread, hs.1]
  have ht : t ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (density_le_scale (by norm_num) hr0)) hb.le) (sq_nonneg _)
  have hbeta : 8 ≤ beta := by dsimp [beta]; nlinarith
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvw : ⟪v, w⟫_ℝ = 0 := by simp [w, b, inner_sub_right, real_inner_smul_right, hvv]
  have hzw : ⟪z, w⟫_ℝ = ‖w‖ ^ 2 := by
    have he : z = w + b • v := by dsimp [w]; module
    calc
      ⟪z, w⟫_ℝ = ⟪w + b • v, w⟫_ℝ := by rw [he]
      _ = ‖w‖ ^ 2 := by simp [inner_add_left, real_inner_smul_left, hvw, real_inner_self_eq_norm_sq]
  have hforce : (8 : ℝ) • z - c • fderiv ℝ (squash 8) z v =
      beta • z - (c * s) • v := by
    rw [squash_fderiv_apply (by norm_num) hz]
    dsimp [beta, t, b, s]
    rw [real_inner_comm z v]
    module
  have hpair : ⟪(8 : ℝ) • z - c • fderiv ℝ (squash 8) z v, w⟫_ℝ =
      beta * ‖w‖ ^ 2 := by
    rw [hforce, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hzw, hvw]
    ring
  have hw : ‖w‖ ≤ 1 / 8 := by
    have hi := real_inner_le_norm ((8 : ℝ) • z - c • fderiv ℝ (squash 8) z v) w
    rw [hpair] at hi
    have hm := mul_le_mul_of_nonneg_right hf (norm_nonneg w)
    have hbetaW := mul_le_mul_of_nonneg_right hbeta (sq_nonneg ‖w‖)
    nlinarith only [hi, hm, hbetaW, norm_nonneg w]
  have hpyth : ‖z‖ ^ 2 = b ^ 2 + ‖w‖ ^ 2 := by
    have he : z = w + b • v := by dsimp [w]; module
    conv_lhs => rw [he, norm_add_sq_real]
    have hwv : ⟪w, v⟫_ℝ = 0 := by rw [real_inner_comm]; exact hvw
    simp only [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs,
      real_inner_smul_right, hwv]
    ring
  have hsr : (8 : ℝ) ≤ ‖z‖ * s := scale_radial_lower (by norm_num) hr
  have hsb : 0 < s * b := by rwa [← hread]
  have hsb1 : s * b < 1 := by rwa [← hread]
  have hsw : s ^ 2 * ‖w‖ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hs.1, hs.2]
    have hw2 : ‖w‖ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by nlinarith only [hw, norm_nonneg w]
    exact (mul_le_of_le_one_left (sq_nonneg ‖w‖) hs2).trans hw2
  have heq : (‖z‖ * s) ^ 2 = (s * b) ^ 2 + s ^ 2 * ‖w‖ ^ 2 := by
    rw [mul_pow, hpyth]
    ring
  nlinarith only [hsr, heq, hsb, hsb1, hsw]

/-- Literal transition exclusion, allowing arbitrarily negative `xi`. -/
theorem transition_exclusion (v z : E) (hv : ‖v‖ = 1) {xi : ℝ}
    (hxi : xi ≤ 1 / 2) (hu0 : 2 / 3 < ⟪v, squash 8 z⟫_ℝ)
    (hu1 : ⟪v, squash 8 z⟫_ℝ < 3 / 4) :
    1 < ‖(8 : ℝ) • z - (8 - xi) • fderiv ℝ (squash 8) z v‖ := by
  by_contra hn
  have hf := le_of_not_gt hn
  have hz := positive_readout_force_inside v z hv (by linarith : 0 ≤ 8 - xi)
    (by linarith) (by linarith) hf
  rw [squash_identity (by norm_num) hz.le] at hu0 hu1
  rw [squash_fderiv_identity (by norm_num) z hz, ContinuousLinearMap.id_apply] at hf
  have hi := norm_inner_le_norm (𝕜 := ℝ) v ((8 : ℝ) • z - (8 - xi) • v)
  rw [Real.norm_eq_abs, hv, one_mul] at hi
  have hb := (abs_le.mp (hi.trans hf)).1
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [inner_sub_right, real_inner_smul_right, hvv, mul_one] at hb
  linarith

end GradientHessian.LatchGeometry
