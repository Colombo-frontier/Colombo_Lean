import SampleReuse.RadialSquaredBounds
import SecondOrder.ScalarLinearScaling

open SecondOrder
open scoped Topology

namespace SampleReuse
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_wall_contDiff (n : ℕ∞) :
    ContDiff ℝ n (fun y : E => radialWallPrimitive ‖y‖) :=
  radial_norm_contDiff (by norm_num : (0:ℝ) < 1/2) radialWallPrimitive_contDiff
    (fun _ hr => radialWallPrimitive_zero hr) n

theorem unit_wall_derivative_bound (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y : E => radialWallPrimitive ‖y‖) x‖ ≤ wallRadialConstant k := by
  by_cases hx : ‖x‖ ≤ 4
  · exact unit_wall_derivative_on_ball k hk3 hx
  have hr : 0 < ‖x‖ := by linarith
  let a : ℝ := 3/‖x‖
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one hr).mpr; linarith
  let A : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  let f : E → ℝ := fun y => radialWallPrimitive ‖y‖
  let c := radialWallPrimitive 1-1
  have hf : ContDiff ℝ k f := unit_wall_contDiff k
  have hA : ‖A‖ ≤ a := by
    dsimp only [A]
    rw [norm_smul a (ContinuousLinearMap.id ℝ E), Real.norm_of_nonneg ha.le]
    exact mul_le_of_le_one_right ha.le ContinuousLinearMap.norm_id_le
  have hAx : ‖A x‖ = 3 := by
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_of_nonneg ha.le]
    dsimp [a]
    field_simp
  have he : f =ᶠ[𝓝 x] (fun y => scalarLinearScaling f a⁻¹ A y+(1-a⁻¹)*c) := by
    have hy : ∀ᶠ y : E in 𝓝 x, 1 < ‖y‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith : 1 < ‖x‖))
    have hAy : ∀ᶠ y : E in 𝓝 x, 1 < ‖A y‖ :=
      (continuous_norm.comp A.continuous).continuousAt.eventually
        (lt_mem_nhds (by rw [hAx]; norm_num : (1:ℝ) < ‖A x‖))
    filter_upwards [hy,hAy] with y hy hAy
    dsimp [f,scalarLinearScaling]
    rw [radialWallPrimitive_tail hy.le, radialWallPrimitive_tail hAy.le]
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_of_nonneg ha.le]
    dsimp [c]
    field_simp
    ring
  rw [iteratedFDeriv_of_eventuallyEq he k,
    iteratedFDeriv_add_apply' (scalarLinearScaling_contDiff hf a⁻¹ A).contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0), Pi.zero_apply, add_zero]
  have hb := scalarLinearScaling_iterated_bound_of_le f (inv_nonneg.mpr ha.le) ha.le
    (wallRadialConstant_pos k).le A hA k hf x
    (unit_wall_derivative_on_ball k hk3 (by rw [hAx]; norm_num))
  have hp : a^k ≤ a := by
    cases k with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1) ha.le).trans_eq (one_mul a)
  have hcoeff : a⁻¹*a^k ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one ha).mpr hp
  exact hb.trans ((mul_le_mul_of_nonneg_right hcoeff (wallRadialConstant_pos k).le).trans_eq (one_mul _))

theorem radiusScaling_norm {R : ℝ} (hR : 0 < R) :
    ‖R⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ R⁻¹ := by
  rw [norm_smul R⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact mul_le_of_le_one_right (inv_nonneg.mpr hR.le) ContinuousLinearMap.norm_id_le

theorem radialCutoffLoss_derivative_bound {R : ℝ} (hR : 0 < R)
    (k : ℕ) (hk : k ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ k (radialCutoffLoss R : E → ℝ) x‖ ≤ (R⁻¹)^k*cutoffRadialConstant k := by
  let A : E →L[ℝ] E := R⁻¹ • ContinuousLinearMap.id ℝ E
  let f : E → ℝ := fun y => radialCutoff ‖y‖
  have hf : ContDiff ℝ k f := radial_norm_contDiff zero_lt_one radialCutoff_contDiff
    (fun _ hr => radialCutoff_one hr) k
  have he : (radialCutoffLoss R : E → ℝ) = scalarLinearScaling f 1 A := by
    funext y
    simp only [radialCutoffLoss,scalarLinearScaling,f,A,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le),
      one_mul,div_eq_mul_inv]
    rw [mul_comm]
  rw [he]
  simpa only [one_mul] using scalarLinearScaling_iterated_bound_of_le f
    zero_le_one (inv_nonneg.mpr hR.le) (cutoffRadialConstant_pos k).le A
    (radiusScaling_norm hR) k hf x (unit_cutoff_derivative_bound k hk (A x))

theorem radialWallLoss_derivative_bound {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R)
    (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ k (radialWallLoss b R : E → ℝ) x‖ ≤
      b*R*(R⁻¹)^k*wallRadialConstant k := by
  let A : E →L[ℝ] E := R⁻¹ • ContinuousLinearMap.id ℝ E
  let f : E → ℝ := fun y => radialWallPrimitive ‖y‖
  have hf : ContDiff ℝ k f := unit_wall_contDiff k
  have he : (radialWallLoss b R : E → ℝ) = scalarLinearScaling f (b*R) A := by
    funext y
    simp only [radialWallLoss,radialWall,scalarLinearScaling,f,A,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le),
      div_eq_mul_inv]
    rw [mul_comm R⁻¹ ‖y‖]
  rw [he]
  exact scalarLinearScaling_iterated_bound_of_le f
    (mul_nonneg hb hR.le) (inv_nonneg.mpr hR.le) (wallRadialConstant_pos k).le A
    (radiusScaling_norm hR) k hf x (unit_wall_derivative_bound k hk1 hk3 (A x))

end
end SampleReuse
