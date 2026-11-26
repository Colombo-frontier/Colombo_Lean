import RandomizedFO2003.SmoothGate
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace RandomizedFO2003.Primitives

open Set Filter
open scoped Topology

/-- One fixed scalar cutoff; its transition lies strictly between squared
radii one and four. -/
noncomputable def radialCutoff (q : ℝ) : ℝ := 1 - gate (q / 12 + 1 / 6)

theorem radialCutoff_contDiff (n : ℕ) : ContDiff ℝ n radialCutoff :=
  contDiff_const.sub ((gate_contDiff n).comp
    ((contDiff_id.div_const 12).add contDiff_const))

theorem radialCutoff_mem (q : ℝ) : 0 ≤ radialCutoff q ∧ radialCutoff q ≤ 1 := by
  dsimp only [radialCutoff]
  constructor <;> linarith [gate_nonneg (q / 12 + 1 / 6), gate_le_one (q / 12 + 1 / 6)]

theorem radialCutoff_one {q : ℝ} (hq : q ≤ 1) : radialCutoff q = 1 := by
  have h := gate_zero_of_le (x := q / 12 + 1 / 6) (by linarith)
  simp only [radialCutoff, h, sub_zero]

theorem radialCutoff_zero {q : ℝ} (hq : 4 ≤ q) : radialCutoff q = 0 := by
  have h := gate_one_of_le (x := q / 12 + 1 / 6) (by linarith)
  simp only [radialCutoff, h, sub_self]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unscaled radial squash. Vanishing outside radius two makes all of
its derivative estimates local to a ball of fixed radius. -/
noncomputable def unitRadialSquash (z : E) : E := radialCutoff (inner (𝕜 := ℝ) z z) • z

theorem unitRadialSquash_contDiff (n : ℕ) : ContDiff ℝ n (unitRadialSquash : E → E) :=
  ((radialCutoff_contDiff n).comp (contDiff_id.inner ℝ contDiff_id)).smul contDiff_id

theorem unitRadialSquash_eq_self {z : E} (hz : ‖z‖ ≤ 1) : unitRadialSquash z = z := by
  have hq : inner (𝕜 := ℝ) z z ≤ 1 := by rw [real_inner_self_eq_norm_sq]; nlinarith [norm_nonneg z]
  simp only [unitRadialSquash, radialCutoff_one hq, one_smul]

theorem unitRadialSquash_zero {z : E} (hz : 2 ≤ ‖z‖) : unitRadialSquash z = 0 := by
  have hq : 4 ≤ inner (𝕜 := ℝ) z z := by rw [real_inner_self_eq_norm_sq]; nlinarith [norm_nonneg z]
  simp only [unitRadialSquash, radialCutoff_zero hq, zero_smul]

theorem unitRadialSquash_norm_le (z : E) : ‖unitRadialSquash z‖ ≤ 2 := by
  by_cases hz : ‖z‖ ≤ 2
  · rw [unitRadialSquash, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (radialCutoff_mem _).1]
    exact (mul_le_of_le_one_left (norm_nonneg z) (radialCutoff_mem _).2).trans hz
  · rw [unitRadialSquash_zero (le_of_not_ge hz), norm_zero]
    norm_num

theorem unitRadialSquash_eventually_zero {z : E} (hz : 2 < ‖z‖) :
    (unitRadialSquash : E → E) =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hz)] with y hy
  exact unitRadialSquash_zero (le_of_lt hy)

/-- Scaling the same fixed radial map preserves dimension-independent
constants. The definition is meaningful for all `B`; properties use `B > 0`. -/
noncomputable def radialSquash (B : ℝ) (z : E) : E := B • unitRadialSquash (B⁻¹ • z)

theorem radialSquash_contDiff (B : ℝ) (n : ℕ) : ContDiff ℝ n (radialSquash B : E → E) :=
  contDiff_const.smul ((unitRadialSquash_contDiff n).comp (contDiff_const.smul contDiff_id))

theorem radialSquash_radial {B : ℝ} (hB : 0 < B) (z : E) :
    radialSquash B z = radialCutoff ((‖z‖ / B) ^ 2) • z := by
  simp only [radialSquash, unitRadialSquash, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
  rw [smul_smul, smul_smul]
  congr 1
  rw [mul_comm (B⁻¹), ← div_eq_mul_inv]
  field_simp

theorem radialSquash_eq_self {B : ℝ} (hB : 0 < B) {z : E} (hz : ‖z‖ ≤ B) :
    radialSquash B z = z := by
  have hs : ‖B⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hB).mpr hz
  rw [radialSquash, unitRadialSquash_eq_self hs, smul_smul, mul_inv_cancel₀ hB.ne', one_smul]

theorem radialSquash_norm_le {B : ℝ} (hB : 0 < B) (z : E) : ‖radialSquash B z‖ ≤ 2 * B := by
  rw [radialSquash, norm_smul, Real.norm_eq_abs, abs_of_pos hB, mul_comm 2 B]
  exact mul_le_mul_of_nonneg_left (unitRadialSquash_norm_le _) hB.le

theorem radialSquash_mem {B : ℝ} (hB : 0 < B) (W : Submodule ℝ E) {z : E} (hz : z ∈ W) :
    radialSquash B z ∈ W := by
  rw [radialSquash_radial hB]
  exact W.smul_mem _ hz

end RandomizedFO2003.Primitives
