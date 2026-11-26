import NCConcave16991.LocalizationScalar
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Dimension-free first-order calculus of the actual integral radial cap

The radius profile is the actual integral of the exponential cutoff from
`LocalizationScalar`. Its derivative is computed, then the radial/tangential
operator is identified and proved to be a contraction. In particular no
dimension-dependent coordinate estimate or assumed Jacobian bound is used.
-/

namespace NCConcave16991.LocalizationRadial

open LocalizationScalar Set
open scoped InnerProductSpace Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialOperator (u : E) (a b : ℝ) : E →L[ℝ] E :=
  a • ContinuousLinearMap.id ℝ E + (b - a) • (innerSL ℝ u).smulRight u

theorem radialOperator_apply (u h : E) (a b : ℝ) :
    radialOperator u a b h = a • h + ((b - a) * ⟪u, h⟫_ℝ) • u := by
  simp [radialOperator, smul_smul]

/-- The radial and tangential eigenvalues independently in `[0,1]` make
the actual radial differential a contraction. -/
theorem radialOperator_norm_le (u : E) (hu : ‖u‖ = 1)
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖radialOperator u a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro h
  have ht : ⟪u, h⟫_ℝ ^ 2 ≤ ‖h‖ ^ 2 := by
    have hh := abs_real_inner_le_norm u h
    rw [hu, one_mul] at hh
    nlinarith [abs_nonneg ⟪u, h⟫_ℝ, sq_abs ⟪u, h⟫_ℝ]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hid : ‖radialOperator u a b h‖ ^ 2 =
      a ^ 2 * (‖h‖ ^ 2 - ⟪u, h⟫_ℝ ^ 2) + b ^ 2 * ⟪u, h⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, radialOperator_apply]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, hu]
    rw [real_inner_comm h u]
    ring
  have hleft := mul_le_mul_of_nonneg_right ha2 (sub_nonneg.mpr ht)
  have hright := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ⟪u, h⟫_ℝ)
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith)

noncomputable def unitDirection (x : E) : E := ‖x‖⁻¹ • x

theorem norm_unitDirection {x : E} (hx : x ≠ 0) : ‖unitDirection x‖ = 1 := by
  simp [unitDirection, norm_smul, norm_ne_zero_iff.mpr hx]

theorem norm_hasFDerivAt {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun z : E => ‖z‖) (innerSL ℝ (unitDirection x)) x := by
  have hsq := (hasFDerivAt_id (𝕜 := ℝ) x).norm_sq
  have hh := hsq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [id_eq] at hh
  have heq : (fun z : E => Real.sqrt (‖z‖ ^ 2)) = fun z => ‖z‖ := by
    funext z
    exact Real.sqrt_sq (norm_nonneg z)
  rw [heq] at hh
  refine hh.congr_fderiv ?_
  ext h
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Real.sqrt_sq (norm_nonneg x), innerSL_apply_apply, unitDirection,
    real_inner_smul_left, smul_eq_mul]
  field_simp
  simp [two_smul]
  ring

noncomputable def radialCap (C : ℝ) (x : E) : E :=
  (radialLength C ‖x‖ / ‖x‖) • x

theorem radialCap_zero (C : ℝ) : radialCap C (0 : E) = 0 := by simp [radialCap]

theorem radialCap_identity {C : ℝ} (hC : 0 < C) {x : E} (hx : ‖x‖ ≤ C) :
    radialCap C x = x := by
  by_cases hz : x = 0
  · subst x
    exact radialCap_zero C
  · rw [radialCap, radialLength_identity hC hx,
      div_self (norm_ne_zero_iff.mpr hz), one_smul]

theorem norm_radialCap (C : ℝ) (x : E) :
    ‖radialCap C x‖ = radialLength C ‖x‖ := by
  by_cases hz : x = 0
  · subst x
    simp [radialCap, radialLength]
  · rw [radialCap, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (radialLength_nonneg (norm_nonneg x)) (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

theorem radialCap_value_bounds {C : ℝ} (hC : 0 < C) (x : E) :
    ‖radialCap C x‖ ≤ min ‖x‖ (2 * C) := by
  rw [norm_radialCap]
  exact le_min (radialLength_le_radius (norm_nonneg x))
    (radialLength_le_cap hC (norm_nonneg x))

theorem radialCap_hasFDerivAt_of_ne_zero {C : ℝ} {x : E} (hx : x ≠ 0) :
    HasFDerivAt (radialCap C)
      (radialOperator (unitDirection x) (radialLength C ‖x‖ / ‖x‖)
        (radialSpeed C ‖x‖)) x := by
  have hn := norm_hasFDerivAt hx
  have hrat := (radialLength_hasDerivAt C ‖x‖).div
    (hasDerivAt_id ‖x‖) (norm_ne_zero_iff.mpr hx)
  have hh := (hrat.comp_hasFDerivAt x hn).smul (hasFDerivAt_id (𝕜 := ℝ) x)
  refine hh.congr_fderiv ?_
  ext h
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply,
    radialOperator_apply, unitDirection, real_inner_smul_left, smul_smul, id_eq]
  congr 1
  field_simp

theorem radialCap_hasFDerivAt_zero {C : ℝ} (hC : 0 < C) :
    HasFDerivAt (radialCap C) (ContinuousLinearMap.id ℝ E) 0 := by
  apply (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) hC] with z hz
  apply radialCap_identity hC
  exact le_of_lt (by simpa using hz)

/-- Actual Jacobian bound for the explicit cap, at every point including 0. -/
theorem radialCap_fderiv_norm_le {C : ℝ} (hC : 0 < C) (x : E) :
    ‖fderiv ℝ (radialCap C) x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    rw [(radialCap_hasFDerivAt_zero hC).fderiv]
    exact ContinuousLinearMap.norm_id_le
  · rw [(radialCap_hasFDerivAt_of_ne_zero hx).fderiv]
    apply radialOperator_norm_le _ (norm_unitDirection hx)
    · exact div_nonneg (radialLength_nonneg (norm_nonneg x)) (norm_nonneg x)
    · exact (div_le_one (norm_pos_iff.mpr hx)).mpr
        (radialLength_le_radius (norm_nonneg x))
    · exact radialSpeed_nonneg C ‖x‖
    · exact radialSpeed_le_one C ‖x‖

theorem radialCap_differentiable {C : ℝ} (hC : 0 < C) : Differentiable ℝ (radialCap C : E → E) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact (radialCap_hasFDerivAt_zero hC).differentiableAt
  · exact (radialCap_hasFDerivAt_of_ne_zero hx).differentiableAt

theorem radialCap_contDiff {C : ℝ} (hC : 0 < C) : ContDiff ℝ ∞ (radialCap C : E → E) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) hC] with z hz
    apply radialCap_identity hC
    exact le_of_lt (by simpa using hz)
  · have hn : ContDiffAt ℝ ∞ (fun z : E => ‖z‖) x := contDiffAt_norm ℝ hx
    exact (((radialLength_contDiff C).contDiffAt.comp x hn).div hn
      (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem radialCap_lipschitz {C : ℝ} (hC : 0 < C) : LipschitzWith 1 (radialCap C : E → E) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (radialCap_differentiable hC)
  intro x
  exact_mod_cast radialCap_fderiv_norm_le hC x

/-- Actual normalized scores are 1-Lipschitz, with no dimension factor. -/
theorem radialCap_score_lipschitz {C : ℝ} (hC : 0 < C) (u : E) (hu : ‖u‖ = 1)
    (x y : E) : |⟪u, radialCap C x⟫_ℝ - ⟪u, radialCap C y⟫_ℝ| ≤ ‖x - y‖ := by
  rw [← inner_sub_right]
  have hh := abs_real_inner_le_norm u (radialCap C x - radialCap C y)
  rw [hu, one_mul] at hh
  exact hh.trans (by simpa [dist_eq_norm] using (radialCap_lipschitz hC).dist_le_mul x y)

theorem radialOperator_isSymmetric (u : E) (a b : ℝ) :
    (radialOperator u a b : E →ₗ[ℝ] E).IsSymmetric := by
  intro x y
  change ⟪radialOperator u a b x, y⟫_ℝ = ⟪x, radialOperator u a b y⟫_ℝ
  simp only [radialOperator_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x u]
  ring

theorem radialCap_fderiv_isSymmetric {C : ℝ} (hC : 0 < C) (x : E) :
    (fderiv ℝ (radialCap C) x : E →ₗ[ℝ] E).IsSymmetric := by
  by_cases hx : x = 0
  · subst x
    rw [(radialCap_hasFDerivAt_zero hC).fderiv]
    exact LinearMap.IsSymmetric.id
  · rw [(radialCap_hasFDerivAt_of_ne_zero hx).fderiv]
    exact radialOperator_isSymmetric _ _ _

theorem radialCap_mem_span (C : ℝ) (x : E) :
    radialCap C x ∈ Submodule.span ℝ ({x} : Set E) := by
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem radialCap_fderiv_mem_span {C : ℝ} (hC : 0 < C) (x y : E) :
    fderiv ℝ (radialCap C) x y ∈ Submodule.span ℝ ({x, y} : Set E) := by
  by_cases hx : x = 0
  · subst x
    rw [(radialCap_hasFDerivAt_zero hC).fderiv]
    exact Submodule.subset_span (by simp)
  · rw [(radialCap_hasFDerivAt_of_ne_zero hx).fderiv, radialOperator_apply,
      unitDirection, smul_smul]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The exact no-new-orientation statement for transpose cap derivatives. -/
theorem radialCap_adjoint_mem_span [CompleteSpace E] {C : ℝ} (hC : 0 < C) (x y : E) :
    (fderiv ℝ (radialCap C) x).adjoint y ∈ Submodule.span ℝ ({x, y} : Set E) := by
  rw [(radialCap_fderiv_isSymmetric hC x).clm_adjoint_eq]
  exact radialCap_fderiv_mem_span hC x y

end NCConcave16991.LocalizationRadial
