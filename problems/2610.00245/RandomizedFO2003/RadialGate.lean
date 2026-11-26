import RandomizedFO2003.RadialDerivativeBounds

namespace RandomizedFO2003.Primitives

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unitRadialSquash_eventually_eq_id {x : E} (hx : ‖x‖ ≤ 1) :
    (unitRadialSquash : E → E) =ᶠ[𝓝 x] id := by
  have hx' : ‖x‖ < (5 / 4 : ℝ) := by linarith
  filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx')] with y hy
  have hq : inner (𝕜 := ℝ) y y ≤ 7 / 4 := by
    rw [real_inner_self_eq_norm_sq]
    have hy' : ‖y‖ < (5 / 4 : ℝ) := hy
    nlinarith [norm_nonneg y]
  have hg := gate_zero_of_le (x := inner (𝕜 := ℝ) y y / 12 + 1 / 6) (by linarith)
  simp only [unitRadialSquash, radialCutoff, hg, sub_zero, one_smul, id_eq]

/-- The closed central ball lies in the identity region's interior. This
also proves the derivative is exactly the identity at its boundary. -/
theorem radialSquash_eventually_eq_id {B : ℝ} (hB : 0 < B) {x : E} (hx : ‖x‖ ≤ B) :
    (radialSquash B : E → E) =ᶠ[𝓝 x] id := by
  have hs : ‖B⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hB).mpr hx
  have ht : Tendsto (fun y : E => B⁻¹ • y) (𝓝 x) (𝓝 (B⁻¹ • x)) :=
    (continuous_const.smul continuous_id).continuousAt
  filter_upwards [(unitRadialSquash_eventually_eq_id hs).comp_tendsto ht] with y hy
  change unitRadialSquash (B⁻¹ • y) = B⁻¹ • y at hy
  simp only [radialSquash, hy, smul_smul, mul_inv_cancel₀ hB.ne', one_smul, id_eq]

theorem radialSquash_hasFDerivAt_identity {B : ℝ} (hB : 0 < B) {x : E} (hx : ‖x‖ ≤ B) :
    HasFDerivAt (radialSquash B : E → E) (ContinuousLinearMap.id ℝ E) x :=
  (radialSquash_eventually_eq_id hB hx).hasFDerivAt_iff.mpr (hasFDerivAt_id x)

theorem radialSquash_fderiv_eq_id {B : ℝ} (hB : 0 < B) {x : E} (hx : ‖x‖ ≤ B) :
    fderiv ℝ (radialSquash B : E → E) x = ContinuousLinearMap.id ℝ E :=
  (radialSquash_hasFDerivAt_identity hB hx).fderiv

theorem radialSquash_readout_ratio {B c : ℝ} (hB : 0 < B) (a x : E)
    (hx : |inner (𝕜 := ℝ) a x| ≤ c * ‖x‖) :
    |inner (𝕜 := ℝ) a (radialSquash B x)| ≤ c * ‖radialSquash B x‖ := by
  rw [radialSquash_radial hB, inner_smul_right, abs_mul,
    norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |radialCutoff ((‖x‖ / B) ^ 2)| * (c * ‖x‖) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = c * (|radialCutoff ((‖x‖ / B) ^ 2)| * ‖x‖) := by ring

noncomputable def radialReadout (a : E) (B α : ℝ) (x : E) : ℝ :=
  inner (𝕜 := ℝ) a (radialSquash B x) / α

theorem radialReadout_contDiff (a : E) (B α : ℝ) (n : ℕ) : ContDiff ℝ n (radialReadout a B α) :=
  (contDiff_const.inner ℝ (radialSquash_contDiff B n)).div_const α

theorem radialReadout_small {B α c : ℝ} (hB : 0 < B) (hα : 0 < α) (hc : 0 ≤ c)
    (hmargin : c * (2 * B) ≤ α / 4) (a x : E)
    (hx : |inner (𝕜 := ℝ) a x| ≤ c * ‖x‖) : |radialReadout a B α x| ≤ 1 / 4 := by
  rw [radialReadout, abs_div, abs_of_pos hα]
  apply (div_le_iff₀ hα).mpr
  calc
    _ ≤ c * ‖radialSquash B x‖ := radialSquash_readout_ratio hB a x hx
    _ ≤ c * (2 * B) := mul_le_mul_of_nonneg_left (radialSquash_norm_le hB x) hc
    _ ≤ α / 4 := hmargin
    _ = 1 / 4 * α := by ring

noncomputable def radialGate (a : E) (B α : ℝ) (x : E) : ℝ := gate (radialReadout a B α x)

theorem radialGate_contDiff (a : E) (B α : ℝ) (n : ℕ) : ContDiff ℝ n (radialGate a B α) :=
  (gate_contDiff n).comp (radialReadout_contDiff a B α n)

/-- A readout below the flat threshold removes all local dependence on the
hidden direction, including every derivative of the composed gate. -/
theorem radialGate_eventually_zero (a : E) (B α : ℝ) {x : E}
    (hx : |radialReadout a B α x| ≤ 1 / 4) : radialGate a B α =ᶠ[𝓝 x] fun _ => 0 := by
  have hlt : radialReadout a B α x < 5 / 16 := by linarith [le_abs_self (radialReadout a B α x)]
  filter_upwards [(radialReadout_contDiff a B α 0).continuous.continuousAt.preimage_mem_nhds
    (Iio_mem_nhds hlt)] with y hy
  exact gate_zero_of_le (le_of_lt hy)

theorem radialGate_zero (a : E) (B α : ℝ) {x : E}
    (hx : |radialReadout a B α x| ≤ 1 / 4) : radialGate a B α x = 0 :=
  (radialGate_eventually_zero a B α hx).self_of_nhds

theorem radialGate_iteratedFDeriv_zero (a : E) (B α : ℝ) {x : E}
    (hx : |radialReadout a B α x| ≤ 1 / 4) (n : ℕ) :
    iteratedFDeriv ℝ n (radialGate a B α) x = 0 := by
  rw [iteratedFDeriv_eq_of_eventuallyEq (radialGate_eventually_zero a B α hx) n,
    iteratedFDeriv_zero_fun, Pi.zero_apply]

end RandomizedFO2003.Primitives
