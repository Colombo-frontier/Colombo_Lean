import SecondOrder.ParametricDerivatives
import SecondOrder.Weights

namespace SecondOrder
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def regularizedGate (δ : ℝ) (f : E → ℝ) (x : E) : ℝ := δ+(1-2*δ)*f x

@[simp] theorem regularizedGate_zero (f : E → ℝ) : regularizedGate 0 f = f := by
  funext x
  simp [regularizedGate]

theorem regularizedGate_contDiff {f : E → ℝ} {k : WithTop ℕ∞}
    (hf : ContDiff ℝ k f) (δ : ℝ) : ContDiff ℝ k (regularizedGate δ f) :=
  contDiff_const.add (contDiff_const.mul hf)

theorem regularizedGate_joint_contDiff {f : E → ℝ} {k : WithTop ℕ∞}
    (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun z : ℝ × E => regularizedGate z.1 f z.2) :=
  contDiff_fst.add ((contDiff_const.sub (contDiff_const.mul contDiff_fst)).mul (hf.comp contDiff_snd))

theorem regularizedGate_interior {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1/2)
    {f : E → ℝ} {x : E} (hf0 : 0 ≤ f x) (hf1 : f x ≤ 1) :
    0 < regularizedGate δ f x ∧ regularizedGate δ f x < 1 := by
  have hc : 0 < 1-2*δ := by linarith
  have hl := mul_nonneg hc.le hf0
  have hu := mul_le_mul_of_nonneg_left hf1 hc.le
  unfold regularizedGate
  constructor <;> linarith

theorem regularizedGate_fderiv {f : E → ℝ} (hf : Differentiable ℝ f) (δ : ℝ) (x : E) :
    fderiv ℝ (regularizedGate δ f) x = (1-2*δ) • fderiv ℝ f x := by
  unfold regularizedGate
  rw [fderiv_const_add, fderiv_const_mul (hf x)]

theorem regularizedGate_second_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (δ : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (regularizedGate δ f)) x = (1-2*δ) • fderiv ℝ (fderiv ℝ f) x := by
  have he := funext (regularizedGate_fderiv (hf.differentiable (by norm_num)) δ)
  rw [he]
  exact fderiv_const_smul
    ((hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x) _

theorem regularizedGate_fisher {f : E → ℝ} (hf : Differentiable ℝ f) {δ ell : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) (x : E)
    (hF : ‖fderiv ℝ f x‖^2 ≤ ell^2*f x*(1-f x)) :
    ‖fderiv ℝ (regularizedGate δ f) x‖^2 ≤
      ell^2*regularizedGate δ f x*(1-regularizedGate δ f x) := by
  rw [regularizedGate_fderiv hf, norm_smul (1-2*δ) (fderiv ℝ f x), Real.norm_eq_abs, mul_pow, sq_abs]
  have hm := mul_le_mul_of_nonneg_left hF (sq_nonneg (1-2*δ))
  have hv := regularized_gate_variance (f x) δ
  have hd : 0 ≤ ell^2*(δ*(1-δ)) := mul_nonneg (sq_nonneg ell) (mul_nonneg hδ0 (by linarith))
  unfold regularizedGate
  nlinarith [congrArg (fun t : ℝ => ell^2*t) hv]

theorem regularizedGate_second_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) (x : E)
    (hH : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ h) :
    ‖fderiv ℝ (fderiv ℝ (regularizedGate δ f)) x‖ ≤ h := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  rw [regularizedGate_second_fderiv hf, norm_smul (1-2*δ) (fderiv ℝ (fderiv ℝ f) x),
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1-2*δ)]
  calc
    _ ≤ 1*‖fderiv ℝ (fderiv ℝ f) x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ h := by simpa only [one_mul] using hH

end
end SecondOrder
