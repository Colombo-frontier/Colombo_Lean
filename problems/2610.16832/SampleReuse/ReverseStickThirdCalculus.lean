import SecondOrder.ProductSecondDerivative

/-! Actual third Fréchet derivatives: scalar product rule for score calculus. -/

open SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def thirdTrilinear (f : E → ℝ) (x u v w : E) : ℝ :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w

theorem thirdTrilinear_eq_iterated (f : E → ℝ) (x u v w : E) :
    thirdTrilinear f x u v w = iteratedFDeriv ℝ 3 f x ![u, v, w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

theorem firstDirectional_differentiable (f : E → ℝ) (hf : ContDiff ℝ 2 f) (v : E) :
    Differentiable ℝ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
      (by norm_num) |>.clm_apply (differentiable_const v)

theorem firstDirectional_fderiv (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x u = secondBilinear f x u v := by
  have hd := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
    (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp [secondBilinear]

theorem secondDirectional_differentiable (f : E → ℝ) (hf : ContDiff ℝ 3 f) (v w : E) :
    Differentiable ℝ (fun x => secondBilinear f x v w) := by
  have hd := ((hf.fderiv_right (show (2 : WithTop ℕ∞) + 1 ≤ 3 by norm_num)).fderiv_right
    (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable (by norm_num)
  exact (hd.clm_apply (differentiable_const v)).clm_apply (differentiable_const w)

theorem secondDirectional_fderiv (f : E → ℝ) (hf : ContDiff ℝ 3 f) (x u v w : E) :
    fderiv ℝ (fun y => secondBilinear f y v w) x u = thirdTrilinear f x u v w := by
  have hd := ((hf.fderiv_right (show (2 : WithTop ℕ∞) + 1 ≤ 3 by norm_num)).fderiv_right
    (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable (by norm_num) x
  unfold secondBilinear
  rw [fderiv_clm_apply (hd.clm_apply (differentiableAt_const v)) (differentiableAt_const w),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simp [thirdTrilinear]

/-- The eight terms of the third scalar product rule, proved for the genuine
iterated Fréchet derivative. No independent derivative fields are assumed. -/
theorem thirdTrilinear_mul (f g : E → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x u v w : E) :
    thirdTrilinear (fun y => f y * g y) x u v w =
      f x * thirdTrilinear g x u v w + g x * thirdTrilinear f x u v w +
      fderiv ℝ f x u * secondBilinear g x v w +
      fderiv ℝ g x u * secondBilinear f x v w +
      fderiv ℝ f x v * secondBilinear g x u w +
      fderiv ℝ g x w * secondBilinear f x u v +
      fderiv ℝ g x v * secondBilinear f x u w +
      fderiv ℝ f x w * secondBilinear g x u v := by
  have hf2 := hf.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hg2 := hg.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have he : (fun y => secondBilinear (fun z => f z * g z) y v w) =
      (fun y => f y * secondBilinear g y v w + g y * secondBilinear f y v w +
        fderiv ℝ f y v * fderiv ℝ g y w + fderiv ℝ g y v * fderiv ℝ f y w) :=
    funext (fun y => secondBilinear_mul hf2 hg2 y v w)
  rw [← secondDirectional_fderiv _ (hf.mul hg), he]
  have hfd := hf.differentiable (by norm_num) x
  have hgd := hg.differentiable (by norm_num) x
  have hfs := secondDirectional_differentiable f hf v w x
  have hgs := secondDirectional_differentiable g hg v w x
  have hfv := firstDirectional_differentiable f hf2 v x
  have hfw := firstDirectional_differentiable f hf2 w x
  have hgv := firstDirectional_differentiable g hg2 v x
  have hgw := firstDirectional_differentiable g hg2 w x
  rw [fderiv_add (((hfd.mul hgs).add (hgd.mul hfs)).add (hfv.mul hgw)) (hgv.mul hfw),
    fderiv_add ((hfd.mul hgs).add (hgd.mul hfs)) (hfv.mul hgw),
    fderiv_add (hfd.mul hgs) (hgd.mul hfs),
    fderiv_mul hfd hgs, fderiv_mul hgd hfs, fderiv_mul hfv hgw, fderiv_mul hgv hfw]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    firstDirectional_fderiv f hf2, firstDirectional_fderiv g hg2,
    secondDirectional_fderiv f hf, secondDirectional_fderiv g hg]
  ring

end
end SampleReuse
