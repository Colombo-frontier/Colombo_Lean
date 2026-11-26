import NCConcave16991.GlobalHardJet

/-! # Derivative difference rules without artificial zeroth-order bounds -/

namespace NCConcave16991.GlobalHard

noncomputable section

open scoped ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem fderiv_sub_bound_comp_contraction (f : E → ℝ) (hf : Differentiable ℝ f)
    (C : ℝ) (hC : 0 ≤ C)
    (hsecond : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖)
    (P : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) (x y : H) :
    ‖fderiv ℝ (fun z ↦ f (P z)) x - fderiv ℝ (fun z ↦ f (P z)) y‖ ≤ C * ‖x - y‖ := by
  have hd (z : H) : fderiv ℝ (fun z ↦ f (P z)) z = (fderiv ℝ f (P z)).comp P :=
    ((hf (P z)).hasFDerivAt.comp z P.hasFDerivAt).fderiv
  have hnorm (z : H) : ‖P z‖ ≤ ‖z‖ :=
    (P.le_opNorm z).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))
  rw [hd, hd, ← ContinuousLinearMap.sub_comp]
  have hh := hsecond (P x) (P y)
  rw [← map_sub] at hh
  have hc := hh.trans (mul_le_mul_of_nonneg_left (hnorm (x - y)) hC)
  exact ((fderiv ℝ f (P x) - fderiv ℝ f (P y)).opNorm_comp_le P).trans
    ((mul_le_mul hc hP (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).trans_eq (mul_one _))

theorem fderiv_sub_bound_add (f g : E → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (C D : ℝ)
    (hCf : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖)
    (hDg : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ D * ‖x - y‖) (x y : E) :
    ‖fderiv ℝ (fun z ↦ f z + g z) x - fderiv ℝ (fun z ↦ f z + g z) y‖ ≤ (C + D) * ‖x - y‖ := by
  rw [fderiv_fun_add (hf x) (hg x), fderiv_fun_add (hf y) (hg y)]
  have he : fderiv ℝ f x + fderiv ℝ g x - (fderiv ℝ f y + fderiv ℝ g y) =
      (fderiv ℝ f x - fderiv ℝ f y) + (fderiv ℝ g x - fderiv ℝ g y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hCf x y) (hDg x y)).trans_eq (by ring))

theorem JetBound.hessian_bound {f : E → ℝ} {A B C : ℝ} (hf : JetBound f A B C) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C :=
  norm_fderiv_le_of_lip' (𝕜 := ℝ) hf.C_nonneg (Filter.Eventually.of_forall (fun y ↦ hf.second y x))

end

end NCConcave16991.GlobalHard
