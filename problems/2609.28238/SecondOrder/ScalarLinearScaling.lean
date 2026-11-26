import SecondOrder.ScalarJetAlgebra

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def scalarLinearScaling (f : F → ℝ) (A : ℝ) (L : E →L[ℝ] F) : E → ℝ := fun x => A*f (L x)

theorem scalarLinearScaling_contDiff {f : F → ℝ} {r : WithTop ℕ∞} (hf : ContDiff ℝ r f)
    (A : ℝ) (L : E →L[ℝ] F) : ContDiff ℝ r (scalarLinearScaling f A L) :=
  contDiff_const.mul (hf.comp L.contDiff)

theorem iteratedFDeriv_linear_bound (f : F → ℝ) (L : E →L[ℝ] F)
    (k : ℕ) (hf : ContDiff ℝ k f) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖*‖L‖^k := by
  rw [L.iteratedFDeriv_comp_right hf x le_rfl]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ k f (L x)) (fun _ => L)

theorem scalarLinearScaling_iterated_bound (f : F → ℝ) (A : ℝ) (L : E →L[ℝ] F)
    (k : ℕ) (hf : ContDiff ℝ k f) (x : E) :
    ‖iteratedFDeriv ℝ k (scalarLinearScaling f A L) x‖ ≤
      |A| *‖L‖^k*‖iteratedFDeriv ℝ k f (L x)‖ := by
  change ‖iteratedFDeriv ℝ k (fun y => A • (f ∘ L) y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.comp L.contDiff).contDiffAt,
    norm_smul A (iteratedFDeriv ℝ k (f ∘ L) x), Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left (iteratedFDeriv_linear_bound f L k hf x) (abs_nonneg A)
  convert hh using 1 <;> ring

theorem scalarLinearScaling_iterated_bound_of_le (f : F → ℝ) {A β M : ℝ}
    (hA : 0≤A) (hβ : 0≤β) (hM : 0≤M) (L : E →L[ℝ] F) (hL : ‖L‖≤β)
    (k : ℕ) (hf : ContDiff ℝ k f) (x : E) (hx : ‖iteratedFDeriv ℝ k f (L x)‖≤M) :
    ‖iteratedFDeriv ℝ k (scalarLinearScaling f A L) x‖ ≤ A*β^k*M := by
  have hh := scalarLinearScaling_iterated_bound f A L k hf x
  rw [abs_of_nonneg hA] at hh
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) hL k) hA)
    hx (norm_nonneg _) (mul_nonneg hA (pow_nonneg hβ k)))

theorem scalarLinearScaling_sub (f g : F → ℝ) (A : ℝ) (L : E →L[ℝ] F) :
    scalarLinearScaling (fun y => f y-g y) A L =
      fun x => scalarLinearScaling f A L x-scalarLinearScaling g A L x := by
  funext x
  exact mul_sub A _ _

end
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem scalarLinearScaling_gradient_bound {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (A : ℝ) (L : E →L[ℝ] F) (x : E) :
    ‖gradient (scalarLinearScaling f A L) x‖ ≤ |A| *‖L‖*‖gradient f (L x)‖ := by
  simp only [norm_gradient_eq_fderiv, ← norm_first_iteratedFDeriv]
  simpa only [pow_one] using scalarLinearScaling_iterated_bound f A L 1 (hf.of_le (by norm_num)) x

theorem scalarLinearScaling_hessian_bound {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (A : ℝ) (L : E →L[ℝ] F) (x : E) :
    ‖fderiv ℝ (gradient (scalarLinearScaling f A L)) x‖ ≤
      |A| *‖L‖^2*‖fderiv ℝ (gradient f) (L x)‖ := by
  simp only [norm_fderiv_gradient]
  exact scalarLinearScaling_iterated_bound f A L 2 hf x

theorem gradient_sub_scalar {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    gradient (fun y => f y-g y) = fun y => gradient f y-gradient g y := by
  funext y
  simp only [gradient, fderiv_sub (hf y) (hg y), map_sub]

theorem hessian_sub_scalar {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (gradient (fun y => f y-g y)) x =
      fderiv ℝ (gradient f) x-fderiv ℝ (gradient g) x := by
  rw [gradient_sub_scalar (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  have hgf : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hgg : ContDiff ℝ 1 (gradient g) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hg.fderiv_right (by norm_num))
  exact fderiv_sub (hgf.differentiable (by norm_num) x) (hgg.differentiable (by norm_num) x)

theorem scalarLinearScaling_gradient_error {f g : F → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (A : ℝ) (L : E →L[ℝ] F) (x : E) :
    ‖gradient (scalarLinearScaling f A L) x-gradient (scalarLinearScaling g A L) x‖ ≤
      |A| *‖L‖*‖gradient f (L x)-gradient g (L x)‖ := by
  have hh := scalarLinearScaling_gradient_bound (hf.sub hg) A L x
  rw [scalarLinearScaling_sub, gradient_sub_scalar
    ((scalarLinearScaling_contDiff hf A L).differentiable (by norm_num))
    ((scalarLinearScaling_contDiff hg A L).differentiable (by norm_num)),
    gradient_sub_scalar (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))] at hh
  exact hh

theorem scalarLinearScaling_hessian_error {f g : F → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (A : ℝ) (L : E →L[ℝ] F) (x : E) :
    ‖fderiv ℝ (gradient (scalarLinearScaling f A L)) x-fderiv ℝ (gradient (scalarLinearScaling g A L)) x‖ ≤
      |A| *‖L‖^2*‖fderiv ℝ (gradient f) (L x)-fderiv ℝ (gradient g) (L x)‖ := by
  have hh := scalarLinearScaling_hessian_bound (hf.sub hg) A L x
  rw [scalarLinearScaling_sub, hessian_sub_scalar (scalarLinearScaling_contDiff hf A L)
    (scalarLinearScaling_contDiff hg A L), hessian_sub_scalar hf hg] at hh
  exact hh

end
end SecondOrder
