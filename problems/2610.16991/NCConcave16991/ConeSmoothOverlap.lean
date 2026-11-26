import NCConcave16991.HessianOverlap

/-! # Actual Hessian summation through a linear family with bounded energy -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open scoped InnerProductSpace BigOperators ContDiff

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem hessian_comp_linear (g : F → ℝ) (hg : ContDiff ℝ 2 g) (P : H →L[ℝ] F) (x : H) :
    fderiv ℝ (fderiv ℝ (fun z ↦ g (P z))) x =
      (fderiv ℝ (fderiv ℝ g) (P x)).bilinearComp P P := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have he : fderiv ℝ (fun z ↦ g (P z)) = fun z ↦ (fderiv ℝ g (P z)).comp P := by
    funext z
    exact ((hd (P z)).hasFDerivAt.comp z P.hasFDerivAt).fderiv
  rw [he]
  have hh := (((ContinuousLinearMap.compL ℝ H F ℝ).flip P).hasFDerivAt).comp x
    (((hD (P x)).hasFDerivAt).comp x P.hasFDerivAt)
  change HasFDerivAt (fun z ↦ (fderiv ℝ g (P z)).comp P) _ x at hh
  rw [hh.fderiv]
  ext h k
  rfl

theorem hessian_add (f g : H → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : H) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f z + g z)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun z ↦ f z + g z) = fun z ↦ fderiv ℝ f z + fderiv ℝ g z := by
    funext z
    exact fderiv_fun_add (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  rw [he]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)

/-- The finite family is made local by its actual linear maps. Its load is
an energy inequality on those maps, so no abstract Hessian-support premise
is supplied for the final construction. -/
theorem hessian_linear_family_bound {ι : Type*} [Fintype ι]
    (g : ι → F → ℝ) (hg : ∀ j, ContDiff ℝ 2 (g j)) (P : ι → H →L[ℝ] F)
    {C load : ℝ} (hC : 0 ≤ C) (hload : 0 ≤ load) (x : H)
    (hlocal : ∀ j, ‖fderiv ℝ (fderiv ℝ (g j)) (P j x)‖ ≤ C)
    (henergy : ∀ h : H, (∑ j, ‖P j h‖ ^ 2) ≤ load * ‖h‖ ^ 2) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ ∑ j, g j (P j z))) x‖ ≤ (C * load) := by
  have hcomp (j : ι) : ContDiff ℝ 2 (fun z ↦ g j (P j z)) := (hg j).comp (P j).contDiff
  rw [HessianOverlap.hessian_sum (fun j z ↦ g j (P j z)) hcomp]
  simp only [hessian_comp_linear _ (hg _) _ _]
  refine HessianOverlap.symmetric_bilinear_norm_le _ ?_ (mul_nonneg hC hload) ?_
  · intro h k
    simp only [sum_apply, ContinuousLinearMap.bilinearComp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    exact ((hg j).contDiffAt.isSymmSndFDerivAt (by norm_num)) _ _
  · intro h
    simp only [sum_apply, ContinuousLinearMap.bilinearComp_apply]
    have ht := norm_sum_le Finset.univ (fun j ↦ fderiv ℝ (fderiv ℝ (g j)) (P j x) (P j h) (P j h))
    simp only [Real.norm_eq_abs] at ht
    have hb (j : ι) : |fderiv ℝ (fderiv ℝ (g j)) (P j x) (P j h) (P j h)| ≤ C * ‖P j h‖ ^ 2 := by
      have hh := (fderiv ℝ (fderiv ℝ (g j)) (P j x)).le_opNorm₂ (P j h) (P j h)
      rw [Real.norm_eq_abs] at hh
      have hn := mul_le_mul_of_nonneg_right (hlocal j) (sq_nonneg ‖P j h‖)
      nlinarith
    have he := mul_le_mul_of_nonneg_left (henergy h) hC
    rw [Finset.mul_sum] at he
    exact ht.trans ((Finset.sum_le_sum (fun j _ ↦ hb j)).trans (by nlinarith))

end NCConcave16991.ConeSmooth
