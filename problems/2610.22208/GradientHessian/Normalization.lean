import GradientHessian.LocalizedNormDerivatives
import GradientHessian.Model

/-! Genuine Hessian regularity and the source normalization b*F(x/b).
The gradient threshold is preserved exactly; the third derivative decreases
by b squared and the initial gap increases by the factor b. -/

noncomputable section
set_option maxSynthPendingDepth 128
namespace GradientHessian.Normalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem curried_third_norm (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ = ‖iteratedFDeriv ℝ 3 f x‖ := by
  rw [← LocalizedNormDerivatives.norm_first_derivative,
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]

theorem hessian_lipschitz_of_third_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (C : NNReal) (hC : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C) :
    LipschitzWith C (fderiv ℝ (fderiv ℝ f)) := by
  have hd : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by norm_num)
  apply lipschitzWith_of_nnnorm_fderiv_le (hdd.differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ C
  rw [curried_third_norm]
  exact hC x

def scaleMap (b : ℝ) : E →L[ℝ] E := b⁻¹ • ContinuousLinearMap.id ℝ E
def rescale (b : ℝ) (f : E → ℝ) (x : E) : ℝ := b * f (b⁻¹ • x)

@[simp] theorem scaleMap_apply (b : ℝ) (x : E) : scaleMap b x = b⁻¹ • x := rfl

theorem scaleMap_norm_le {b : ℝ} (hb : 0<b) : ‖scaleMap (E := E) b‖ ≤ b⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hb).le
  intro x
  simp only [scaleMap_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  exact le_rfl

theorem rescale_contDiff (b : ℝ) {f : E → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (rescale b f) := contDiff_const.mul (hf.comp (scaleMap b).contDiff)

theorem rescale_zero (b : ℝ) (f : E → ℝ) : rescale b f 0 = b*f 0 := by simp [rescale]

theorem rescale_fderiv {b : ℝ} (hb : b≠0) {f : E → ℝ} (hf : Differentiable ℝ f) (x : E) :
    fderiv ℝ (rescale b f) x = fderiv ℝ f (b⁻¹ • x) := by
  have h := ((hf (scaleMap b x)).hasFDerivAt.comp x (scaleMap b).hasFDerivAt).const_mul b
  have he : b • ((fderiv ℝ f (scaleMap b x)).comp (scaleMap b)) = fderiv ℝ f (b⁻¹ • x) := by
    ext y
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      scaleMap_apply, map_smul, smul_eq_mul]
    field_simp
  convert h.fderiv using 1
  exact he.symm

theorem rescale_hessian {b : ℝ} (hb : b≠0) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (fderiv ℝ (rescale b f)) x = b⁻¹ • fderiv ℝ (fderiv ℝ f) (b⁻¹ • x) := by
  have he : fderiv ℝ (rescale b f) = fun z => fderiv ℝ f (scaleMap b z) :=
    funext (rescale_fderiv hb (hf.differentiable (by norm_num)))
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable (by norm_num)
  have h := ((hd (scaleMap b x)).hasFDerivAt.comp x (scaleMap b).hasFDerivAt).fderiv
  simp only [Function.comp_def] at h
  rw [he, h]
  ext v w
  simp only [ContinuousLinearMap.comp_apply, scaleMap_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem rescale_ordinaryJet {b : ℝ} (hb : b≠0) {f : E → ℝ}
    (hf : Differentiable ℝ f) (x : E) :
    JetLocality.ordinaryJet (rescale b f) x =
      (b * (JetLocality.ordinaryJet f (b⁻¹ • x)).1,
        (JetLocality.ordinaryJet f (b⁻¹ • x)).2) := by
  simp only [JetLocality.ordinaryJet, rescale, rescale_fderiv hb hf]

theorem rescale_richJet {b : ℝ} (hb : b≠0) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x : E) :
    JetLocality.richJet (rescale b f) x =
      (b * (JetLocality.richJet f (b⁻¹ • x)).1,
        (JetLocality.richJet f (b⁻¹ • x)).2.1,
        b⁻¹ • (JetLocality.richJet f (b⁻¹ • x)).2.2) := by
  simp only [JetLocality.richJet, rescale_fderiv hb (hf.differentiable (by norm_num)),
    rescale_hessian hb hf, rescale]

theorem rescale_derivative_bound {b C : ℝ} (hb : 0<b) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {n : ℕ} (hn : n≤3) (hC : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ n (rescale b f) x‖ ≤ b * C * (b⁻¹)^n := by
  have he : rescale b f = b • (f ∘ scaleMap b) := rfl
  rw [he, iteratedFDeriv_const_smul_apply
      ((hf.comp (scaleMap b).contDiff).of_le (by exact_mod_cast hn : (n:WithTop ℕ∞)≤3)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_pos hb,
    (scaleMap b).iteratedFDeriv_comp_right hf x (by exact_mod_cast hn)]
  have hnorm := (iteratedFDeriv ℝ n f (scaleMap b x)).norm_compContinuousLinearMap_le
    (fun _ => scaleMap (E := E) b)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hnorm
  have hp := pow_le_pow_left₀ (norm_nonneg (scaleMap (E := E) b)) (scaleMap_norm_le hb) n
  have hinner : ‖(iteratedFDeriv ℝ n f (scaleMap b x)).compContinuousLinearMap (fun _ => scaleMap b)‖ ≤
      C*(b⁻¹)^n :=
    hnorm.trans (mul_le_mul (hC (scaleMap b x)) hp (by positivity)
      (le_trans (norm_nonneg (iteratedFDeriv ℝ n f (scaleMap b x))) (hC (scaleMap b x))))
  have hout := mul_le_mul_of_nonneg_left hinner hb.le
  simpa only [mul_assoc] using hout

theorem rescale_third_le_one {b C : ℝ} (hb : 0<b) (hCb : C≤b^2)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) (hC : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ 3 (rescale b f) x‖ ≤ 1 := by
  have h := rescale_derivative_bound hb hf (n := 3) le_rfl hC x
  have hc := mul_le_mul_of_nonneg_left hCb hb.le
  have hi := mul_le_mul_of_nonneg_right hc (show 0≤(b⁻¹)^3 by positivity)
  have he : b*b^2*(b⁻¹)^3 = 1 := by field_simp; ring
  rw [he] at hi
  exact h.trans hi

theorem rescale_lower {b lower : ℝ} (hb : 0≤b) {f : E → ℝ}
    (hf : ∀ x, lower≤f x) (x : E) : b*lower ≤ rescale b f x :=
  mul_le_mul_of_nonneg_left (hf _) hb

theorem rescale_stationary {d : ℕ} {b : ℝ} (hb : b≠0) {f : Model.Point d → ℝ}
    (hf : Differentiable ℝ f) (x : Model.Point d) :
    x ∈ Model.stationary (rescale b f) ↔ b⁻¹ • x ∈ Model.stationary f := by
  simp only [Model.stationary, Set.mem_setOf_eq, rescale_fderiv hb hf]

theorem rescale_admissible {d : ℕ} {b C lower T : ℝ} (hb : 0<b) (hCb : C≤b^2)
    {f : Model.Point d → ℝ} (hf : ContDiff ℝ 3 f)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C) (hl : ∀ x, lower≤f x)
    (hg : b*(f 0-lower)≤T) : Model.Admissible T (rescale b f) := by
  apply Model.admissible_of_lower_bound
    ((rescale_contDiff b hf).of_le (by decide : (2:WithTop ℕ∞)≤3))
    (rescale_lower hb.le hl)
  · rw [rescale_zero]
    linarith
  · exact hessian_lipschitz_of_third_bound (rescale_contDiff b hf) 1
      (rescale_third_le_one hb hCb hf hC)

end GradientHessian.Normalization
