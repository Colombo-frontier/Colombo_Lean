import SphereSmoothingRadialCutoff
open MeasureTheory Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing

/-- Exact real Hilbert norm derivative away from zero. -/
theorem hasFDerivAt_norm_explicit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (hx : x ≠ 0) : HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hh := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have heq : ((1/(2*Real.sqrt (‖x‖^2))) • (2 • innerSL ℝ x)) = ‖x‖⁻¹ • innerSL ℝ x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Real.sqrt_sq_eq_abs, abs_norm]
    congr 1
    field_simp [hn]
    <;> norm_num
  rw [heq] at hh
  simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hh

theorem radialCutoff_hasFDerivAt_inside {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ ε : ℝ} (hε : 0 < ε) {x : E} (hx : ‖x‖ < ρ) :
    HasFDerivAt (radialCutoff (E := E) ρ ε) (0 : E →L[ℝ] ℝ) x := by
  have heq : radialCutoff (E := E) ρ ε =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) hx] with y hy
    exact radialCutoff_eq_one hε hy.le
  exact (hasFDerivAt_const (1:ℝ) x).congr_of_eventuallyEq heq

theorem radialCutoff_hasFDerivAt_outside {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ ε : ℝ} (hε : 0 < ε) {x : E} (hx : ρ+ε < ‖x‖) :
    HasFDerivAt (radialCutoff (E := E) ρ ε) (0 : E →L[ℝ] ℝ) x := by
  have heq : radialCutoff (E := E) ρ ε =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) hx] with y hy
    exact radialCutoff_eq_zero hε hy.le
  exact (hasFDerivAt_const (0:ℝ) x).congr_of_eventuallyEq heq

/-- The cutoff derivative on the actual annulus, including the exact normal
factor 1/(epsilon*norm x). -/
theorem radialCutoff_hasFDerivAt_annulus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) {x : E}
    (hx₁ : ρ < ‖x‖) (hx₂ : ‖x‖ < ρ+ε) :
    HasFDerivAt (radialCutoff (E := E) ρ ε) ((-(ε*‖x‖)⁻¹) • innerSL ℝ x) x := by
  have hxne : x ≠ 0 := norm_pos_iff.1 (hρ.trans hx₁)
  have heq : radialCutoff (E := E) ρ ε =ᶠ[𝓝 x] (fun y : E => (ρ+ε-‖y‖)/ε) := by
    have hmem : {y : E | ρ < ‖y‖ ∧ ‖y‖ < ρ+ε} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const) |>.mem_nhds ⟨hx₁,hx₂⟩
    filter_upwards [hmem] with y hy
    have ha : 0 < (ρ+ε-‖y‖)/ε := div_pos (by linarith [hy.2]) hε
    have hb : (ρ+ε-‖y‖)/ε < 1 := (div_lt_one hε).2 (by linarith [hy.1])
    dsimp only [radialCutoff]
    rw [min_eq_right hb.le, max_eq_right ha.le]
  have hh := ((hasFDerivAt_norm_explicit x hxne).const_sub (ρ+ε)).const_smul ε⁻¹
  have hh' : HasFDerivAt (fun y : E => (ρ+ε-‖y‖)/ε)
      ((-(ε*‖x‖)⁻¹) • innerSL ℝ x) x := by
    convert! hh using 1
    · funext y
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    · simp only [smul_neg, smul_smul, ← neg_smul]
      congr 1
      simp only [mul_inv_rev]
      ring

  exact hh'.congr_of_eventuallyEq heq

end Task006.SphereSmoothing
