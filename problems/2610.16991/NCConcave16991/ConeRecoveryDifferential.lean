import NCConcave16991.ConeClockGap
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Actual derivatives of the cone clock and exit gate

These derivatives are taken from the literal functions, including at zero
perpendicular displacement. The square-root regularizers stay strictly positive.
-/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicular_inner (v u : E) (hv : ‖v‖ = 1) :
    ⟪perpendicular v u, v⟫_ℝ = 0 := by
  simp [perpendicular, inner_sub_left, real_inner_smul_left,
    hv]

theorem norm_sq_decomposition (v u : E) (hv : ‖v‖ = 1) :
    ‖u‖ ^ 2 = ⟪u, v⟫_ℝ ^ 2 + ‖perpendicular v u‖ ^ 2 := by
  rw [perpendicular, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hv, one_pow, mul_one, real_inner_smul_right]
  ring

def perpendicularOperator (v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ v).smulRight v

theorem perpendicularOperator_apply (v u : E) :
    perpendicularOperator v u = perpendicular v u := by
  simp [perpendicularOperator, perpendicular, real_inner_comm]

theorem perpendicular_hasFDerivAt (v u : E) :
    HasFDerivAt (perpendicular v) (perpendicularOperator v) u := by
  have hf : (fun x ↦ perpendicularOperator v x) = perpendicular v :=
    funext (perpendicularOperator_apply v)
  rw [← hf]
  exact (perpendicularOperator v).hasFDerivAt

theorem sqrt_norm_sq_hasFDerivAt {a : ℝ} (ha : 0 < a) (u : E) :
    HasFDerivAt (fun x : E ↦ Real.sqrt (a + ‖x‖ ^ 2))
      ((Real.sqrt (a + ‖u‖ ^ 2))⁻¹ • innerSL ℝ u) u := by
  have hp : 0 < a + ‖u‖ ^ 2 := by positivity
  have hs : Real.sqrt (a + ‖u‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hh := ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_add a).sqrt hp.ne'
  refine hh.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp <;> simp [smul_eq_mul]

theorem sqrt_perpendicular_hasFDerivAt {a : ℝ} (ha : 0 < a) (v u : E)
    (hv : ‖v‖ = 1) :
    HasFDerivAt (fun x : E ↦ Real.sqrt (a + ‖perpendicular v x‖ ^ 2))
      ((Real.sqrt (a + ‖perpendicular v u‖ ^ 2))⁻¹ •
        innerSL ℝ (perpendicular v u)) u := by
  have hh := (sqrt_norm_sq_hasFDerivAt ha (perpendicular v u)).comp u
    (perpendicular_hasFDerivAt v u)
  refine hh.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, perpendicularOperator_apply]
  have hi : ⟪perpendicular v u, perpendicular v h⟫_ℝ = ⟪perpendicular v u, h⟫_ℝ := by
    change ⟪perpendicular v u, h - ⟪h, v⟫_ℝ • v⟫_ℝ = _
    rw [inner_sub_right, real_inner_smul_right, perpendicular_inner v u hv]
    simp
  rw [hi]

def clockArgument (v z u : E) : ℝ :=
  ⟪u, v⟫_ℝ - Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) + 4 * latch ⟪zeta z, v⟫_ℝ

def gateArgument (q : ℝ) (v u : E) : ℝ :=
  (⟪u, v⟫_ℝ - Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2)) / q

def clockUGradient (q : ℝ) (v z u : E) : E :=
  ((Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ + q⁻¹) • u -
    (10 * omega (clockArgument v z u)) •
      (v - (Real.sqrt (1 + ‖perpendicular v u‖ ^ 2))⁻¹ • perpendicular v u)

def gateUGradient (q : ℝ) (v u : E) : E :=
  (density (gateArgument q v u - 1) / q) •
    (v - (Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2))⁻¹ • perpendicular v u)

theorem clock_hasFDerivAt_u {q : ℝ} (hq : 0 < q) (v z u : E) (hv : ‖v‖ = 1) :
    HasFDerivAt (clock q v z) (innerSL ℝ (clockUGradient q v z u)) u := by
  have ht : HasFDerivAt (fun x : E ↦ ⟪x, v⟫_ℝ) (innerSL ℝ v) u := by
    have hh := (innerSL ℝ v).hasFDerivAt (x := u)
    change HasFDerivAt (fun x ↦ ⟪v, x⟫_ℝ) (innerSL ℝ v) u at hh
    simpa only [real_inner_comm v] using hh
  have ha := (ht.sub (sqrt_perpendicular_hasFDerivAt (by norm_num : (0 : ℝ) < 1) v u hv)).add_const
    (4 * latch ⟪zeta z, v⟫_ℝ)
  have htheta := (theta_hasDerivAt (clockArgument v z u)).comp_hasFDerivAt u ha
  have hquad : HasFDerivAt (fun x : E ↦ ‖x‖ ^ 2 / (2 * q))
      ((2 * q)⁻¹ • (2 • innerSL ℝ u)) u := by
    simpa only [div_eq_mul_inv] using
      ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.mul_const ((2 * q)⁻¹))
  have hh := (((sqrt_norm_sq_hasFDerivAt (by norm_num : (0 : ℝ) < 1) u).sub_const 1).add
    hquad).sub (htheta.const_mul 10)
  refine hh.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    clockUGradient, inner_sub_left, inner_add_left, real_inner_smul_left]
  field_simp
  ring

theorem exitGate_hasFDerivAt {q : ℝ} (hq : 0 < q) (v u : E) (hv : ‖v‖ = 1) :
    HasFDerivAt (exitGate q v) (innerSL ℝ (gateUGradient q v u)) u := by
  have ht : HasFDerivAt (fun x : E ↦ ⟪x, v⟫_ℝ) (innerSL ℝ v) u := by
    have hh := (innerSL ℝ v).hasFDerivAt (x := u)
    change HasFDerivAt (fun x ↦ ⟪v, x⟫_ℝ) (innerSL ℝ v) u at hh
    simpa only [real_inner_comm v] using hh
  have ha := (ht.sub (sqrt_perpendicular_hasFDerivAt (sq_pos_of_pos hq) v u hv)).mul_const q⁻¹
  simp only [← div_eq_mul_inv] at ha
  have hh := (exitStep_hasDerivAt (gateArgument q v u)).comp_hasFDerivAt u ha
  refine hh.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, gateUGradient, inner_sub_left,
    real_inner_smul_left]
  ring

variable [CompleteSpace E]

theorem clock_hasGradientAt_u {q : ℝ} (hq : 0 < q) (v z u : E) (hv : ‖v‖ = 1) :
    HasGradientAt (clock q v z) (clockUGradient q v z u) u :=
  clock_hasFDerivAt_u hq v z u hv

theorem exitGate_hasGradientAt {q : ℝ} (hq : 0 < q) (v u : E) (hv : ‖v‖ = 1) :
    HasGradientAt (exitGate q v) (gateUGradient q v u) u :=
  exitGate_hasFDerivAt hq v u hv

end NCConcave16991.ConeRecovery
