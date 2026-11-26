/- Adapted from the proved radial-calculus fragments in ../0105_formalization/Manuscript0105/RadialDerivativeBounds.lean. No assumed lower bounds are imported. -/
import NCConcave16991.DenseSmoothRadialBasics
import Mathlib.Tactic.Module

/-!
# Scalar estimates for radial higher derivatives

These inequalities are the dimension-free scalar core of Lemma `lem:radial-third`.
-/

namespace NCConcave16991.DenseSmooth

open scoped InnerProductSpace

/-- The two terms in the operator-norm estimate for the radial Hessian sum to at most `2`. -/
theorem radialHessian_scalar_bound {r : ℝ} (hr : 0 ≤ r) :
    3 * r / (Real.sqrt (1 + r ^ 2)) ^ 3 +
        3 * r ^ 3 / (Real.sqrt (1 + r ^ 2)) ^ 5 ≤ 2 := by
  let d : ℝ := Real.sqrt (1 + r ^ 2)
  have hs : 0 < 1 + r ^ 2 := by positivity
  have hd : 0 < d := Real.sqrt_pos.2 hs
  have hd2 : d ^ 2 = 1 + r ^ 2 := by simpa [d] using Real.sq_sqrt hs.le
  have hcombine :
      3 * r / d ^ 3 + 3 * r ^ 3 / d ^ 5 =
        (3 * r * (1 + 2 * r ^ 2)) / d ^ 5 := by
    field_simp
    nlinarith [hd2]
  rw [hcombine]
  apply (div_le_iff₀ (pow_pos hd 5)).2
  have hpoly :
      0 ≤ 4 + 11 * r ^ 2 + 4 * r ^ 4 + 4 * r ^ 6 +
        20 * r ^ 8 + 4 * r ^ 10 := by positivity
  have hsquare :
      (3 * r * (1 + 2 * r ^ 2)) ^ 2 ≤ (2 * d ^ 5) ^ 2 := by
    rw [show (2 * d ^ 5) ^ 2 = 4 * d ^ 10 by ring]
    rw [show d ^ 10 = (1 + r ^ 2) ^ 5 by
      calc
        d ^ 10 = (d ^ 2) ^ 5 := by ring
        _ = (1 + r ^ 2) ^ 5 := by rw [hd2]]
    nlinarith
  have hleft : 0 ≤ 3 * r * (1 + 2 * r ^ 2) := by positivity
  have hright : 0 ≤ 2 * d ^ 5 := by positivity
  nlinarith

/-- The four linewise bounds `3+9+9+15=36` in the third-derivative formula. -/
theorem radialThird_scalar_lines {r : ℝ} (hr : 0 ≤ r) :
    3 / (Real.sqrt (1 + r ^ 2)) ^ 3 ≤ 3 ∧
      9 * r ^ 2 / (Real.sqrt (1 + r ^ 2)) ^ 5 ≤ 9 ∧
      9 * r ^ 2 / (Real.sqrt (1 + r ^ 2)) ^ 5 ≤ 9 ∧
      15 * r ^ 4 / (Real.sqrt (1 + r ^ 2)) ^ 7 ≤ 15 := by
  let d : ℝ := Real.sqrt (1 + r ^ 2)
  have hs : 0 < 1 + r ^ 2 := by positivity
  have hd : 0 < d := Real.sqrt_pos.2 hs
  have hd2 : d ^ 2 = 1 + r ^ 2 := by simpa [d] using Real.sq_sqrt hs.le
  have hdOne : 1 ≤ d := by
    nlinarith [sq_nonneg (d - 1)]
  have hrD : r ≤ d := by
    nlinarith [sq_nonneg (d - r)]
  have hd2d5 : d ^ 2 ≤ d ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hdOne 3
    nlinarith [pow_pos hd 2]
  have hd4d7 : d ^ 4 ≤ d ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hdOne 3
    nlinarith [pow_pos hd 4]
  have hr2d5 : r ^ 2 ≤ d ^ 5 := by
    exact (pow_le_pow_left₀ hr hrD 2).trans hd2d5
  have hr4d7 : r ^ 4 ≤ d ^ 7 := by
    exact (pow_le_pow_left₀ hr hrD 4).trans hd4d7
  change 3 / d ^ 3 ≤ 3 ∧ 9 * r ^ 2 / d ^ 5 ≤ 9 ∧
    9 * r ^ 2 / d ^ 5 ≤ 9 ∧ 15 * r ^ 4 / d ^ 7 ≤ 15
  constructor
  · apply (div_le_iff₀ (pow_pos hd 3)).2
    have : 1 ≤ d ^ 3 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hdOne 3
    nlinarith
  constructor
  · apply (div_le_iff₀ (pow_pos hd 5)).2
    nlinarith
  constructor
  · apply (div_le_iff₀ (pow_pos hd 5)).2
    nlinarith
  · apply (div_le_iff₀ (pow_pos hd 7)).2
    nlinarith

theorem radialThird_scalar_total {r : ℝ} (hr : 0 ≤ r) :
    3 / (Real.sqrt (1 + r ^ 2)) ^ 3 +
      9 * r ^ 2 / (Real.sqrt (1 + r ^ 2)) ^ 5 +
      9 * r ^ 2 / (Real.sqrt (1 + r ^ 2)) ^ 5 +
      15 * r ^ 4 / (Real.sqrt (1 + r ^ 2)) ^ 7 ≤ 36 := by
  obtain ⟨h1, h2, h3, h4⟩ := radialThird_scalar_lines hr
  linarith

section HessianAction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear Hessian formula from equation `(radial-hessian-formula)`, evaluated at a
direction `h`. -/
noncomputable def radialHessianAction (u z h : E) : E :=
  let d := Real.sqrt (1 + ‖z‖ ^ 2)
  ((-(d⁻¹ ^ 3)) •
      (⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h)) +
    ((3 * ⟪u, z⟫_ℝ * d⁻¹ ^ 5 * ⟪z, h⟫_ℝ) • z)

/-- The radial Hessian as a continuous linear operator. -/
noncomputable def radialHessian (u z : E) : E →L[ℝ] E :=
  let d := Real.sqrt (1 + ‖z‖ ^ 2)
  (-(d⁻¹ ^ 3)) •
      ((innerSL ℝ u).smulRight z + (innerSL ℝ z).smulRight u +
        ⟪u, z⟫_ℝ • ContinuousLinearMap.id ℝ E) +
    (3 * ⟪u, z⟫_ℝ * d⁻¹ ^ 5) • (innerSL ℝ z).smulRight z

noncomputable def radialHessianPow (u z : E) : E →L[ℝ] E :=
  let s : ℝ := 1 + ‖z‖ ^ 2
  (-(s ^ (-(3 / 2 : ℝ)))) • (innerSL ℝ z).smulRight u -
    (s ^ (-(3 / 2 : ℝ))) • (innerSL ℝ u).smulRight z -
    (⟪u, z⟫_ℝ * s ^ (-(3 / 2 : ℝ))) • ContinuousLinearMap.id ℝ E +
    (3 * ⟪u, z⟫_ℝ * s ^ (-(5 / 2 : ℝ))) • (innerSL ℝ z).smulRight z

theorem radialHessianPow_eq (u z : E) : radialHessianPow u z = radialHessian u z := by
  let s : ℝ := 1 + ‖z‖ ^ 2
  let d : ℝ := Real.sqrt s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hspos : 0 < s := by dsimp [s]; positivity
  have hdpos : 0 < d := Real.sqrt_pos.2 hspos
  have hd2 : d ^ 2 = s := by simpa [d] using Real.sq_sqrt hs
  have h3 : s ^ (-(3 / 2 : ℝ)) = d⁻¹ ^ 3 := by
    rw [Real.rpow_neg hs, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hspos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    change (s * d)⁻¹ = d⁻¹ ^ 3
    field_simp [hdpos.ne']
    nlinarith
  have h5 : s ^ (-(5 / 2 : ℝ)) = d⁻¹ ^ 5 := by
    rw [Real.rpow_neg hs, show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add hspos, Real.rpow_two, ← Real.sqrt_eq_rpow]
    change (s ^ 2 * d)⁻¹ = d⁻¹ ^ 5
    field_simp [hdpos.ne']
    nlinarith
  dsimp [radialHessianPow, radialHessian]
  change
    (-(s ^ (-(3 / 2 : ℝ)))) • (innerSL ℝ z).smulRight u -
        (s ^ (-(3 / 2 : ℝ))) • (innerSL ℝ u).smulRight z -
        (⟪u, z⟫_ℝ * s ^ (-(3 / 2 : ℝ))) • ContinuousLinearMap.id ℝ E +
        (3 * ⟪u, z⟫_ℝ * s ^ (-(5 / 2 : ℝ))) • (innerSL ℝ z).smulRight z =
      (-(d⁻¹ ^ 3)) •
          ((innerSL ℝ u).smulRight z + (innerSL ℝ z).smulRight u +
            ⟪u, z⟫_ℝ • ContinuousLinearMap.id ℝ E) +
        (3 * ⟪u, z⟫_ℝ * d⁻¹ ^ 5) • (innerSL ℝ z).smulRight z
  rw [h3, h5]
  module

theorem radialHessian_apply (u z h : E) :
    radialHessian u z h = radialHessianAction u z h := by
  dsimp [radialHessian, radialHessianAction]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  module

theorem hasFDerivAt_radialCoordinateGradient (u z : E) :
    HasFDerivAt (radialCoordinateGradient u) (radialHessian u z) z := by
  let s : E → ℝ := fun x ↦ 1 + ‖x‖ ^ 2
  have hbase : HasFDerivAt s (2 • innerSL ℝ z) z := by
    simpa [s] using ((hasFDerivAt_id z).norm_sq).const_add 1
  have hspos : 0 < s z := by dsimp [s]; positivity
  have ha := hbase.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hspos.ne')
  have hb := hbase.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hspos.ne')
  have hc : HasFDerivAt (fun x : E ↦ ⟪u, x⟫_ℝ) (innerSL ℝ u) z :=
    (innerSL ℝ u).hasFDerivAt
  have hfirst := ha.smul_const u
  have hscalar := hc.mul hb
  have hsecond := hscalar.smul (hasFDerivAt_id z)
  rw [← radialHessianPow_eq]
  convert hfirst.sub hsecond using 1
  · funext x
    rfl
  · ext h
    dsimp [radialHessianPow, s]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply]
    ring_nf
    module

/-- Dimension-free operator estimate for the displayed radial Hessian formula. -/
theorem norm_radialHessianAction_le_two
    {u : E} (hu : ‖u‖ = 1) (z h : E) :
    ‖radialHessianAction u z h‖ ≤ 2 * ‖h‖ := by
  let r : ℝ := ‖z‖
  let d : ℝ := Real.sqrt (1 + r ^ 2)
  have hr : 0 ≤ r := norm_nonneg z
  have hd : 0 < d := Real.sqrt_pos.2 (by dsimp [r]; positivity)
  have huh : |⟪u, h⟫_ℝ| ≤ ‖h‖ := by
    simpa [hu] using abs_real_inner_le_norm u h
  have hzh : |⟪z, h⟫_ℝ| ≤ r * ‖h‖ := by
    simpa [r] using abs_real_inner_le_norm z h
  have huz : |⟪u, z⟫_ℝ| ≤ r := by
    simpa [hu, r] using abs_real_inner_le_norm u z
  have hsum :
      ‖⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h‖ ≤
        3 * r * ‖h‖ := by
    calc
      ‖⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h‖
          ≤ ‖⟪u, h⟫_ℝ • z‖ + ‖⟪z, h⟫_ℝ • u‖ + ‖⟪u, z⟫_ℝ • h‖ := by
            exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = |⟪u, h⟫_ℝ| * r + |⟪z, h⟫_ℝ| + |⟪u, z⟫_ℝ| * ‖h‖ := by
        simp [norm_smul, Real.norm_eq_abs, hu, r]
      _ ≤ ‖h‖ * r + (r * ‖h‖) + r * ‖h‖ := by gcongr
      _ = 3 * r * ‖h‖ := by ring
  have hfirst :
      ‖-(d⁻¹ ^ 3) •
          (⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h)‖ ≤
        (3 * r / d ^ 3) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (pow_pos (inv_pos.2 hd) 3)]
    calc
      d⁻¹ ^ 3 *
          ‖⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h‖
          ≤ d⁻¹ ^ 3 * (3 * r * ‖h‖) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (3 * r / d ^ 3) * ‖h‖ := by field_simp
  have hlast :
      ‖(3 * ⟪u, z⟫_ℝ * d⁻¹ ^ 5 * ⟪z, h⟫_ℝ) • z‖ ≤
        (3 * r ^ 3 / d ^ 5) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_pos (pow_pos (inv_pos.2 hd) 5)]
    change 3 * |⟪u, z⟫_ℝ| * d⁻¹ ^ 5 * |⟪z, h⟫_ℝ| * r ≤
      (3 * r ^ 3 / d ^ 5) * ‖h‖
    calc
      3 * |⟪u, z⟫_ℝ| * d⁻¹ ^ 5 * |⟪z, h⟫_ℝ| * r
          ≤ 3 * r * d⁻¹ ^ 5 * (r * ‖h‖) * r := by gcongr
      _ = (3 * r ^ 3 / d ^ 5) * ‖h‖ := by field_simp
  dsimp [radialHessianAction]
  change ‖-(d⁻¹ ^ 3) •
      (⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h) +
    (3 * ⟪u, z⟫_ℝ * d⁻¹ ^ 5 * ⟪z, h⟫_ℝ) • z‖ ≤ 2 * ‖h‖
  calc
    _ ≤ ‖-(d⁻¹ ^ 3) •
          (⟪u, h⟫_ℝ • z + ⟪z, h⟫_ℝ • u + ⟪u, z⟫_ℝ • h)‖ +
        ‖(3 * ⟪u, z⟫_ℝ * d⁻¹ ^ 5 * ⟪z, h⟫_ℝ) • z‖ := norm_add_le _ _
    _ ≤ (3 * r / d ^ 3) * ‖h‖ + (3 * r ^ 3 / d ^ 5) * ‖h‖ :=
      add_le_add hfirst hlast
    _ = (3 * r / d ^ 3 + 3 * r ^ 3 / d ^ 5) * ‖h‖ := by ring
    _ ≤ 2 * ‖h‖ :=
      mul_le_mul_of_nonneg_right (by simpa [d, r] using radialHessian_scalar_bound hr)
        (norm_nonneg h)

theorem norm_radialHessian_le_two
    {u : E} (hu : ‖u‖ = 1) (z : E) : ‖radialHessian u z‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  rw [radialHessian_apply]
  exact norm_radialHessianAction_le_two hu z h

end HessianAction

end NCConcave16991.DenseSmooth
