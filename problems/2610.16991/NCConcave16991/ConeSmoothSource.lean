import NCConcave16991.ConeSmoothLocalRules
import NCConcave16991.ConeSmoothRadial
import NCConcave16991.GlobalHardVectorJets

/-! # Actual source-coupling estimates on the enlarged dual cylinder -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial Set Metric
open scoped ContDiff InnerProductSpace

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def dualCylinder (Q : H →L[ℝ] E) (R : ℝ) : Set H := {x | ‖Q x‖ ≤ 2 * R}

theorem dualCylinder_convex (Q : H →L[ℝ] E) (R : ℝ) : Convex ℝ (dualCylinder Q R) := by
  have hh := (convex_closedBall (0 : E) (2 * R)).linear_preimage Q.toLinearMap
  convert hh using 1
  ext x
  simp only [dualCylinder, mem_setOf_eq, mem_preimage, mem_closedBall, dist_zero_right,
    ContinuousLinearMap.coe_coe]

def sourceFunction (n : ℕ) (R : ℝ) (w : E) (P Q : H →L[ℝ] E) (x : H) : ℝ :=
  R⁻¹ * ⟪zeta (P x) - Real.sqrt (n : ℝ) • w, Q x⟫_ℝ

theorem sourceFunction_localJet (n : ℕ) {R q : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q)
    (hrel : Real.sqrt (n : ℝ) = q * R) (w : E) (hw : ‖w‖ = 1)
    (P Q : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    LocalJetBound (dualCylinder Q R) (sourceFunction n R w P Q)
      (2 * (3 + Real.sqrt (n : ℝ))) (6 * q) 12 := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hnormP (x : H) : ‖P x‖ ≤ ‖x‖ :=
    (P.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))
  have hnormQ (x : H) : ‖Q x‖ ≤ ‖x‖ :=
    (Q.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
  let f : H → E := fun x ↦ zeta (P x) - Real.sqrt (n : ℝ) • w
  let D : H → H →L[ℝ] E := fun x ↦ (fderiv ℝ (zeta : E → E) (P x)).comp P
  have hf (x : H) : HasFDerivAt f (D x) x :=
    ((zeta_differentiable (P x)).hasFDerivAt.comp x P.hasFDerivAt).sub_const _
  have hfv (x : H) : ‖f x‖ ≤ 3 + Real.sqrt (n : ℝ) := by
    have hh := norm_sub_le (zeta (P x)) (Real.sqrt (n : ℝ) • w)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hw, mul_one] at hh
    exact hh.trans (by linarith [zeta_norm_bound (P x)])
  have hfl (x y : H) : ‖f x - f y‖ ≤ ‖x - y‖ := by
    have he : f x - f y = zeta (P x) - zeta (P y) := by dsimp [f]; abel
    rw [he]
    exact (zeta_sub_bound _ _).trans (by simpa only [← map_sub] using hnormP (x - y))
  have hD (x : H) : ‖D x‖ ≤ 1 := by
    exact ((fderiv ℝ (zeta : E → E) (P x)).opNorm_comp_le P).trans
      ((mul_le_mul (zeta_fderiv_norm_le _) hP (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring))
  have hDl (x y : H) : ‖D x - D y‖ ≤ 5 * ‖x - y‖ := by
    dsimp only [D]
    rw [← ContinuousLinearMap.sub_comp]
    have hh := zeta_fderiv_sub_bound (P x) (P y)
    rw [← map_sub] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left (hnormP (x - y)) (by norm_num : (0 : ℝ) ≤ 5))
    exact ((fderiv ℝ (zeta : E → E) (P x) - fderiv ℝ (zeta : E → E) (P y)).opNorm_comp_le P).trans
      ((mul_le_mul hb hP (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
  let T : H → H →L[ℝ] ℝ := fun x ↦ (innerSL ℝ (f x)).comp Q + (innerSL ℝ (Q x)).comp (D x)
  have hT (x : H) : HasFDerivAt (fun x ↦ ⟪f x, Q x⟫_ℝ) (T x) x := by
    have hh := (hf x).inner ℝ Q.hasFDerivAt
    refine hh.congr_fderiv ?_
    ext h
    simp only [T, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    rw [real_inner_comm (D x h) (Q x)]
  have hd (x : H) : fderiv ℝ (sourceFunction n R w P Q) x = R⁻¹ • T x :=
    ((hT x).const_mul R⁻¹).fderiv
  have hfirst (x : H) (hx : x ∈ dualCylinder Q R) : ‖T x‖ ≤ (3 + Real.sqrt (n : ℝ)) + 2 * R := by
    have ht := (norm_add_le _ _).trans (add_le_add
      ((innerSL ℝ (f x)).opNorm_comp_le Q) ((innerSL ℝ (Q x)).opNorm_comp_le (D x)))
    simp only [innerSL_apply_norm] at ht
    have h1 := mul_le_mul (hfv x) hQ (norm_nonneg _) (by positivity : 0 ≤ 3 + Real.sqrt (n : ℝ))
    have h2 := mul_le_mul hx (hD x) (norm_nonneg _) (by positivity : 0 ≤ 2 * R)
    exact ht.trans (by nlinarith)
  have hsecond (x : H) (hx : x ∈ dualCylinder Q R) (y : H) (hy : y ∈ dualCylinder Q R) :
      ‖T x - T y‖ ≤ (10 * R + 2) * ‖x - y‖ := by
    have he : T x - T y =
        ((innerSL ℝ (f x)).comp Q - (innerSL ℝ (f y)).comp Q) +
          ((innerSL ℝ (Q x)).comp (D x) - (innerSL ℝ (Q y)).comp (D y)) := by dsimp [T]; abel
    rw [he]
    have h1 := GlobalHard.VectorJetBound.inner_term_sub_estimate (f x) (f y) Q Q
    simp only [sub_self, norm_zero, mul_zero, zero_add] at h1
    have hb1 := mul_le_mul (hfl x y) hQ (norm_nonneg _) (norm_nonneg (x - y))
    have h2 := GlobalHard.VectorJetBound.inner_term_sub_estimate (Q x) (Q y) (D x) (D y)
    have hb21 := mul_le_mul hx (hDl x y) (norm_nonneg _) (by positivity : 0 ≤ 2 * R)
    have hb22 := mul_le_mul (hnormQ (x - y)) (hD y) (norm_nonneg _) (norm_nonneg (x - y))
    rw [map_sub] at hb22
    exact (norm_add_le _ _).trans (by nlinarith)
  refine ⟨contDiff_const.mul (((zeta_contDiff.comp P.contDiff).sub contDiff_const).inner ℝ Q.contDiff),
    by positivity, by positivity, by norm_num, ?_, ?_, ?_⟩
  · intro x hx
    have hi := abs_real_inner_le_norm (f x) (Q x)
    have hb := mul_le_mul (hfv x) hx (norm_nonneg _) (by positivity : 0 ≤ 3 + Real.sqrt (n : ℝ))
    change |R⁻¹ * ⟪f x, Q x⟫_ℝ| ≤ _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR0)]
    have hh := mul_le_mul_of_nonneg_left (hi.trans hb) (inv_nonneg.mpr hR0.le)
    have he : R⁻¹ * ((3 + Real.sqrt (n : ℝ)) * (2 * R)) = 2 * (3 + Real.sqrt (n : ℝ)) := by field_simp
    exact he ▸ hh
  · intro x hx
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
    have hn : (3 + Real.sqrt (n : ℝ)) + 2 * R ≤ (6 * q) * R := by
      have hh := mul_le_mul_of_nonneg_right hq hR0.le
      rw [hrel]
      nlinarith
    have hh := mul_le_mul_of_nonneg_left ((hfirst x hx).trans hn) (inv_nonneg.mpr hR0.le)
    have he : R⁻¹ * ((6 * q) * R) = 6 * q := by field_simp
    exact he ▸ hh
  · intro x hx y hy
    rw [hd, hd, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
    have hh := mul_le_mul_of_nonneg_left (hsecond x hx y hy) (inv_nonneg.mpr hR0.le)
    have hn : R⁻¹ * (10 * R + 2) ≤ 12 := by
      apply (inv_mul_le_iff₀ hR0).mpr
      linarith
    have hb := mul_le_mul_of_nonneg_right hn (norm_nonneg (x - y))
    exact hh.trans (by nlinarith)

end NCConcave16991.ConeSmooth
