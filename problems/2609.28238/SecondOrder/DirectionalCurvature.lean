import SecondOrder.LocalHessian

open scoped BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def secondQuadratic (f : E → ℝ) (x v : E) : ℝ := iteratedFDeriv ℝ 2 f x (fun _ => v)

theorem secondQuadratic_eq (f : E → ℝ) (x v : E) :
    secondQuadratic f x v = fderiv ℝ (fderiv ℝ f) x v v := iteratedFDeriv_two_apply _ _ _

@[simp] theorem secondQuadratic_zero (f : E → ℝ) (x : E) : secondQuadratic f x 0 = 0 := by
  rw [secondQuadratic_eq, map_zero]

theorem secondQuadratic_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x v : E) :
    secondQuadratic (fun y => f y+g y) x v = secondQuadratic f x v+secondQuadratic g x v := by
  simp only [secondQuadratic, iteratedFDeriv_add_apply' hf.contDiffAt hg.contDiffAt,
    ContinuousMultilinearMap.add_apply]

theorem secondQuadratic_sum {ι : Type*} [Fintype ι] (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x v : E) :
    secondQuadratic (fun y => ∑ i, f i y) x v = ∑ i, secondQuadratic (f i) x v := by
  unfold secondQuadratic
  rw [iteratedFDeriv_sum (fun i (_ : i ∈ Finset.univ) => hf i)]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]

theorem secondQuadratic_const_mul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x v : E) :
    secondQuadratic (fun y => c*f y) x v = c*secondQuadratic f x v := by
  change (iteratedFDeriv ℝ 2 (fun y => c • f y) x) (fun _ => v) = _
  rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt]
  rfl

theorem secondQuadratic_comp_linear {f : F → ℝ} (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (x v : E) :
    secondQuadratic (f ∘ L) x v = secondQuadratic f (L x) (L v) := by
  unfold secondQuadratic
  rw [L.iteratedFDeriv_comp_right hf x le_rfl]
  rfl

theorem secondQuadratic_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x v : E) :
    secondQuadratic (fun y => f y*g y) x v =
      f x*secondQuadratic g x v+g x*secondQuadratic f x v+
      2*(fderiv ℝ f x v)*(fderiv ℝ g x v) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hff := (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have hgf := (hg.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun y => f y*g y) = fun y => f y • fderiv ℝ g y+g y • fderiv ℝ f y :=
    funext (fun y => ((hfd y).hasFDerivAt.mul (hgd y).hasFDerivAt).fderiv)
  have hd := (((hfd x).hasFDerivAt.smul (hgf x).hasFDerivAt).add
    ((hgd x).hasFDerivAt.smul (hff x).hasFDerivAt)).fderiv
  rw [secondQuadratic_eq, he, hd, secondQuadratic_eq, secondQuadratic_eq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The diagonal second Fréchet derivative is the quadratic form of the actual Hessian. -/
theorem secondQuadratic_eq_inner {f : H → ℝ} (hf : ContDiff ℝ 2 f) (x v : H) :
    secondQuadratic f x v = ⟪fderiv ℝ (gradient f) x v,v⟫_ℝ := by
  let R := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) x).hasFDerivAt
  have he : fderiv ℝ (gradient f) x = R.comp (fderiv ℝ (fderiv ℝ f) x) :=
    (R.hasFDerivAt.comp x hd).fderiv
  rw [he, secondQuadratic_eq]
  change _ = ⟪(InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (fderiv ℝ f) x v),v⟫_ℝ
  rw [InnerProductSpace.toDual_symm_apply]

end Hilbert
end
end SecondOrder
