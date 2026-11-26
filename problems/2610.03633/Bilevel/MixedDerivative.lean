import Bilevel.JointDerivative
import Bilevel.JointVectorDerivative
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Mixed derivative interchange under the original primitive assumptions

Directional finite differences in the lower variable have uniformly convergent
outer derivatives. Differentiating their limit establishes the opposite mixed
derivative without requiring an `xx` Hessian or strengthening the model to C².
-/

noncomputable section
open scoped RealInnerProductSpace Topology
open Filter Asymptotics

namespace Bilevel.MixedDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaled_error_bound {a b : E} {t C : ℝ} (ht : 0 < t)
    (he : ‖a - t • b‖ ≤ C * t ^ 2) : ‖t⁻¹ • a - b‖ ≤ C * t := by
  have hid : t⁻¹ • a - b = t⁻¹ • (a - t • b) := by
    simp [smul_sub, smul_smul, ht.ne']
  rw [hid, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  calc
    t⁻¹ * ‖a - t • b‖ ≤ t⁻¹ * (C * t ^ 2) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht.le)
    _ = C * t := by field_simp; ring

def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem step_pos (n : ℕ) : 0 < step n := by unfold step; positivity

theorem step_tendsto : Tendsto step atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

omit [NormedSpace ℝ E] in
/-- A uniform error bounded by a constant times `step n` tends uniformly to zero. -/
theorem uniform_of_step_bound {Z : Type*} (f : ℕ → Z → E) (g : Z → E) (C : ℝ)
    (h : ∀ n z, ‖f n z - g z‖ ≤ C * step n) : TendstoUniformly f g atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hc : Tendsto (fun n => C * step n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul step_tendsto
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn z
  rw [dist_eq_norm, norm_sub_rev]
  exact (h n z).trans_lt hn

end Bilevel.MixedDerivative

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem gy_lipschitz_y (x : X) (y z : Y) :
    ‖P.gy x y - P.gy x z‖ ≤ Lg * ‖y - z‖ := by
  apply JointDerivative.component_bound P.Lg_nonneg (norm_nonneg (y - z))
    (v := P.gx x y - P.gx x z)
  have h := P.smooth_g x x y z
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  linarith

/-- The scalar directional derivative in y is differentiable in x. -/
theorem hasGradient_inner_gy (x : X) (y v : Y) :
    HasGradientAt (fun z => ⟪P.gy z y, v⟫) (P.gxy x y v) x := by
  let t := MixedDerivative.step
  let F : ℕ → X → ℝ := fun n z => (t n)⁻¹ * (P.g z (y + t n • v) - P.g z y)
  let D : ℕ → X → X →L[ℝ] ℝ := fun n z =>
    InnerProductSpace.toDual ℝ X ((t n)⁻¹ • (P.gx z (y + t n • v) - P.gx z y))
  let q : X → ℝ := fun z => ⟪P.gy z y, v⟫
  let Q : X → X →L[ℝ] ℝ := fun z => InnerProductSpace.toDual ℝ X (P.gxy z y v)
  have hF : ∀ n z, HasFDerivAt (F n) (D n z) z := by
    intro n z
    have h := ((P.has_gx z (y + t n • v)).hasFDerivAt.sub
      (P.has_gx z y).hasFDerivAt).const_smul ((t n)⁻¹)
    simpa only [F, D, map_smul, map_sub, smul_eq_mul] using h
  have hq : ∀ n z, ‖F n z - q z‖ ≤ (Lg / 2 * ‖v‖ ^ 2) * t n := by
    intro n z
    have h := JointDerivative.gradient_taylor (P.g z) (P.gy z) Lg
      (P.has_gy z) (P.gy_lipschitz_y z) y (t n • v)
    rw [real_inner_smul_right, norm_smul,
      Real.norm_of_nonneg (MixedDerivative.step_pos n).le] at h
    have he : ‖P.g z (y + t n • v) - P.g z y - t n • ⟪P.gy z y, v⟫‖ ≤
        (Lg / 2 * ‖v‖ ^ 2) * (t n) ^ 2 := by
      simpa only [smul_eq_mul] using h.trans_eq (by ring)
    simpa only [F, q, smul_eq_mul] using
      MixedDerivative.scaled_error_bound (MixedDerivative.step_pos n) he
  have hD : ∀ n z, ‖D n z - Q z‖ ≤ (ρ / 2 * ‖v‖ ^ 2) * t n := by
    intro n z
    have h := FrozenTilt.taylor_remainder_bound (P.gx z) (P.gxy z) y (t n • v) ρ
      (P.has_gxy z) (P.variation_xy_at_x z)
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (MixedDerivative.step_pos n)] at h
    have he : ‖P.gx z (y + t n • v) - P.gx z y - t n • P.gxy z y v‖ ≤
        (ρ / 2 * ‖v‖ ^ 2) * (t n) ^ 2 := h.trans_eq (by ring)
    have hb := MixedDerivative.scaled_error_bound (MixedDerivative.step_pos n) he
    simpa only [D, Q, ← map_sub, LinearIsometryEquiv.norm_map] using hb
  have hFu := MixedDerivative.uniform_of_step_bound F q (Lg / 2 * ‖v‖ ^ 2) hq
  have hDu := MixedDerivative.uniform_of_step_bound D Q (ρ / 2 * ‖v‖ ^ 2) hD
  exact hasGradientAt_iff_hasFDerivAt.mpr
    (hasFDerivAt_of_tendstoUniformly hDu hF (fun z => hFu.tendsto_at z) x)

theorem mixed_hessian_variation_x (x z : X) (y : Y) :
    ‖P.gxy x y - P.gxy z y‖ ≤ ρ * ‖x - z‖ := by
  simpa [jointDistance] using P.variation_xy x z y y

/-- Directional testing of the mixed Taylor remainder. -/
theorem mixed_directional_remainder (x dx : X) (y v : Y) :
    ‖⟪P.gy (x + dx) y - P.gy x y - (P.gxy x y).adjoint dx, v⟫‖ ≤
      (ρ / 2 * ‖dx‖ ^ 2) * ‖v‖ := by
  have hlip : ∀ z w, ‖P.gxy z y v - P.gxy w y v‖ ≤ (ρ * ‖v‖) * ‖z - w‖ := by
    intro z w
    calc
      ‖P.gxy z y v - P.gxy w y v‖ = ‖(P.gxy z y - P.gxy w y) v‖ := rfl
      _ ≤ ‖P.gxy z y - P.gxy w y‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ρ * ‖z - w‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (P.mixed_hessian_variation_x z w y) (norm_nonneg v)
      _ = (ρ * ‖v‖) * ‖z - w‖ := by ring
  have h := JointDerivative.gradient_taylor (fun z => ⟪P.gy z y, v⟫)
    (fun z => P.gxy z y v) (ρ * ‖v‖) (fun z => P.hasGradient_inner_gy z y v) hlip x dx
  have hid : ⟪P.gy (x + dx) y - P.gy x y - (P.gxy x y).adjoint dx, v⟫ =
      ⟪P.gy (x + dx) y, v⟫ - ⟪P.gy x y, v⟫ - ⟪P.gxy x y v, dx⟫ := by
    rw [inner_sub_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left, real_inner_comm dx]
  rw [hid]
  exact h.trans_eq (by ring)

/-- The opposite mixed derivative has a vector-valued quadratic remainder. -/
theorem gy_x_taylor (x dx : X) (y : Y) :
    ‖P.gy (x + dx) y - P.gy x y - (P.gxy x y).adjoint dx‖ ≤ ρ / 2 * ‖dx‖ ^ 2 := by
  let w := P.gy (x + dx) y - P.gy x y - (P.gxy x y).adjoint dx
  have h := P.mixed_directional_remainder x dx y w
  change ‖⟪w, w⟫‖ ≤ (ρ / 2 * ‖dx‖ ^ 2) * ‖w‖ at h
  rw [real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg ‖w‖)] at h
  change ‖w‖ ≤ ρ / 2 * ‖dx‖ ^ 2
  by_cases hw : ‖w‖ = 0
  · rw [hw]
    exact mul_nonneg (div_nonneg P.ρ_nonneg (by norm_num)) (sq_nonneg _)
  · have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    nlinarith

/-- Mixed-partial interchange, derived without existence of an xx Hessian. -/
theorem has_gyx (x : X) (y : Y) :
    HasFDerivAt (fun z => P.gy z y) (P.gxy x y).adjoint x := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply IsBigO.trans_isLittleO _ (isLittleO_norm_pow_id (E' := X) one_lt_two)
  apply IsBigO.of_bound (ρ / 2)
  apply Filter.Eventually.of_forall
  intro dx
  rw [Real.norm_of_nonneg (sq_nonneg ‖dx‖)]
  exact P.gy_x_taylor x dx y

/-- The lower stationarity map has the required joint derivative under
the original primitive assumptions. -/
theorem has_joint_gy (x : X) (y : Y) :
    HasFDerivAt (fun p : X × Y => P.gy p.1 p.2)
      ((P.gxy x y).adjoint.comp (ContinuousLinearMap.fst ℝ X Y) +
        (P.gyy x y).comp (ContinuousLinearMap.snd ℝ X Y)) (x, y) := by
  apply JointVectorDerivative.hasFDerivAt_joint P.gy (fun z w => (P.gxy z w).adjoint)
    P.gyy P.ρ_nonneg P.has_gyx P.has_gyy
  · intro z w v
    simpa only [← map_sub, LinearIsometryEquiv.norm_map] using P.mixed_hessian_variation_x z w v
  · intro z v w
    simpa only [← map_sub, LinearIsometryEquiv.norm_map] using P.variation_xy_at_x z v w
  · exact P.variation_yy_at_x

end Bilevel.Model.Primitive
