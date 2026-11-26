import NCConcave16991.ConeRecoveryDifferential
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The concrete guard excludes every exterior source block -/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def capAdjoint (z a : E) : E := (fderiv ℝ (zeta : E → E) z).adjoint a

theorem capAdjoint_norm_le (z a : E) : ‖capAdjoint z a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖(fderiv ℝ (zeta : E → E) z).adjoint‖ * ‖a‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (zeta : E → E) z‖ * ‖a‖ := by simp
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (zeta_fderiv_norm_le z) (norm_nonneg a)
    _ = _ := one_mul _

def clockZGradient (v z u : E) : E :=
  -(160 * omega (clockArgument v z u) * density (4 * ⟪zeta z, v⟫_ℝ - 1)) • capAdjoint z v

theorem clock_hasFDerivAt_z (q : ℝ) (v z u : E) :
    HasFDerivAt (fun x : E ↦ clock q v x u) (innerSL ℝ (clockZGradient v z u)) z := by
  have ht : HasFDerivAt (fun x : E ↦ ⟪zeta x, v⟫_ℝ)
      ((innerSL ℝ v).comp (fderiv ℝ (zeta : E → E) z)) z := by
    have hh := (innerSL ℝ v).hasFDerivAt.comp z (zeta_differentiable z).hasFDerivAt
    change HasFDerivAt (fun x : E ↦ ⟪v, zeta x⟫_ℝ) _ z at hh
    simpa only [real_inner_comm v] using hh
  have hH := (latch_hasDerivAt ⟪zeta z, v⟫_ℝ).comp_hasFDerivAt z ht
  have ha := (hH.const_mul 4).const_add
    (⟪u, v⟫_ℝ - Real.sqrt (1 + ‖perpendicular v u‖ ^ 2))
  have htheta := (theta_hasDerivAt (clockArgument v z u)).comp_hasFDerivAt z ha
  have hh := (htheta.const_mul 10).const_sub
    (Real.sqrt (1 + ‖u‖ ^ 2) - 1 + ‖u‖ ^ 2 / (2 * q))
  refine hh.congr_fderiv ?_
  ext h
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    neg_apply, clockZGradient, real_inner_smul_left, capAdjoint,
    ContinuousLinearMap.adjoint_inner_left, smul_eq_mul]
  rw [real_inner_comm v]
  ring

theorem clock_hasGradientAt_z (q : ℝ) (v z u : E) :
    HasGradientAt (fun x : E ↦ clock q v x u) (clockZGradient v z u) z :=
  clock_hasFDerivAt_z q v z u

theorem clockZGradient_norm_le (v z u : E) (hv : ‖v‖ = 1) :
    ‖clockZGradient v z u‖ ≤ 320 := by
  have ho : 0 ≤ omega (clockArgument v z u) := omega_nonneg _
  have hd : 0 ≤ density (4 * ⟪zeta z, v⟫_ℝ - 1) := density_nonneg _
  have hcoeff : 0 ≤ 160 * omega (clockArgument v z u) *
      density (4 * ⟪zeta z, v⟫_ℝ - 1) := by positivity
  have hcoeff_le : 160 * omega (clockArgument v z u) *
      density (4 * ⟪zeta z, v⟫_ℝ - 1) ≤ 320 := by
    have hh := mul_le_mul (omega_le_one (clockArgument v z u))
      (density_le_two (4 * ⟪zeta z, v⟫_ℝ - 1)) hd (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  calc
    _ = (160 * omega (clockArgument v z u) * density (4 * ⟪zeta z, v⟫_ℝ - 1)) *
        ‖capAdjoint z v‖ := by
      simp only [clockZGradient, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hcoeff]
    _ ≤ (160 * omega (clockArgument v z u) * density (4 * ⟪zeta z, v⟫_ℝ - 1)) * 1 :=
      mul_le_mul_of_nonneg_left (by simpa only [hv] using capAdjoint_norm_le z v) hcoeff
    _ ≤ 320 := by simpa only [mul_one] using hcoeff_le

/-- The source term is the actual adjoint derivative of the capped affine
coupling, with its permitted unit-ball multiplier. -/
def sourceZGradient (gate : ℝ) (z a : E) : E := gate • capAdjoint z a

theorem source_hasFDerivAt_z (gate : ℝ) (v z a : E) :
    HasFDerivAt (fun x : E ↦ gate * ⟪zeta x - v, a⟫_ℝ)
      (innerSL ℝ (sourceZGradient gate z a)) z := by
  have ht := (innerSL ℝ a).hasFDerivAt.comp z (zeta_differentiable z).hasFDerivAt
  have hh := (ht.sub_const ⟪a, v⟫_ℝ).const_mul gate
  have hf : (fun x : E ↦ gate * (⟪a, zeta x⟫_ℝ - ⟪a, v⟫_ℝ)) =
      (fun x : E ↦ gate * ⟪zeta x - v, a⟫_ℝ) := by
    funext x
    simp [inner_sub_left, real_inner_comm]
  change HasFDerivAt (fun x : E ↦ gate * (⟪a, zeta x⟫_ℝ - ⟪a, v⟫_ℝ)) _ z at hh
  rw [hf] at hh
  refine hh.congr_fderiv ?_
  ext h
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    sourceZGradient, real_inner_smul_left, capAdjoint, ContinuousLinearMap.adjoint_inner_left,
    smul_eq_mul]

theorem source_hasGradientAt_z (gate : ℝ) (v z a : E) :
    HasGradientAt (fun x : E ↦ gate * ⟪zeta x - v, a⟫_ℝ) (sourceZGradient gate z a) z :=
  source_hasFDerivAt_z gate v z a

theorem adjacent_source_coefficient_bound (v z a : E) (hv : ‖v‖ = 1) (ha : ‖a‖ ≤ 1) :
    |⟪zeta z - v, a⟫_ℝ| ≤ 4 := by
  have hr : ‖zeta z - v‖ ≤ 4 := (norm_sub_le _ _).trans (by linarith [zeta_norm_bound z])
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul hr ha (norm_nonneg a) (by norm_num)).trans (by norm_num))

theorem sourceZGradient_norm_le {gate : ℝ} (hg : 0 ≤ gate ∧ gate ≤ 1)
    (z a : E) (ha : ‖a‖ ≤ 1) : ‖sourceZGradient gate z a‖ ≤ 1 := by
  rw [sourceZGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg hg.1]
  have hn : ‖capAdjoint z a‖ ≤ 1 := (capAdjoint_norm_le z a).trans ha
  exact (mul_le_mul hg.2 hn (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem guard_of_small_concrete_block (v z u a : E) (hv : ‖v‖ = 1)
    {gate : ℝ} (hg : 0 ≤ gate ∧ gate ≤ 1) (ha : ‖a‖ ≤ 1)
    (hsmall : ‖gradient (ConeRadial.guard 3000) z + clockZGradient v z u +
      sourceZGradient gate z a‖ ≤ 1 / 1000) : ‖z‖ < 2 := by
  apply guard_separation z (clockZGradient v z u + sourceZGradient gate z a)
  · have hc := clockZGradient_norm_le v z u hv
    have hs := sourceZGradient_norm_le hg z a ha
    exact (norm_add_le _ _).trans (by linarith)
  · simpa only [add_assoc] using hsmall

end NCConcave16991.ConeRecovery
