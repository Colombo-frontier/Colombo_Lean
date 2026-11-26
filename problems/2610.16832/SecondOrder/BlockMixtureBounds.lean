import SecondOrder.RegularizedMixture

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Closed-interval version of the finite-mixture estimate, including gates
equal to zero or one. The same constants survive regularization. -/
theorem blockMixture_bounds (p : ι → E → ℝ)
    (V : (ι → Bool) → HomogeneousBlocks ι E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x : HomogeneousBlocks ι E) (hp0 : ∀ i, 0 ≤ p i (x i)) (hp1 : ∀ i, p i (x i) ≤ 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ w, |V w x| ≤ v₀) (hder : ∀ w, ‖gradient (V w) x‖ ≤ v₁)
    (hsecond : ∀ w, ‖fderiv ℝ (gradient (V w)) x‖ ≤ v₂)
    (hF : ∀ i, ‖gradient (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (gradient (p i)) (x i)‖ ≤ h) :
    let N := bernoulliMixture (fun i (y : HomogeneousBlocks ι E) => p i (y i)) V
    ContDiff ℝ 2 N ∧ |N x| ≤ v₀ ∧
      ‖gradient N x‖ ≤ v₁+v₀*ell ∧
      ‖fderiv ℝ (gradient N) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
  letI : NormedSpace ℝ (HomogeneousBlocks ι E) := inferInstance
  let q := fun i (y : HomogeneousBlocks ι E) => p i (y i)
  have hq (i : ι) : ContDiff ℝ 2 (q i) := (hp i).comp (blockProj (E := E) i).contDiff
  have hb (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1/2) :
      ‖fderiv ℝ (regularizedMixture q V δ) x‖ ≤ v₁+v₀*ell ∧
      ‖fderiv ℝ (fderiv ℝ (regularizedMixture q V δ)) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
    have hFδ (i : ι) : ‖gradient (regularizedGate δ (p i)) (x i)‖^2 ≤
        ell^2*regularizedGate δ (p i) (x i)*(1-regularizedGate δ (p i) (x i)) := by
      rw [norm_gradient_eq_fderiv]
      apply regularizedGate_fisher ((hp i).differentiable (by norm_num)) hδ0.le hδ1.le
      simpa only [norm_gradient_eq_fderiv] using hF i
    have hHδ (i : ι) : ‖fderiv ℝ (gradient (regularizedGate δ (p i))) (x i)‖ ≤ h := by
      rw [norm_hessian_eq_second_fderiv]
      apply regularizedGate_second_bound (hp i) hδ0.le hδ1.le
      simpa only [norm_hessian_eq_second_fderiv] using hH i
    have hi := blockMixture_interior (fun i => regularizedGate δ (p i)) V
      (fun i => regularizedGate_contDiff (hp i) δ) hV x
      (fun i => (regularizedGate_interior hδ0 hδ1 (hp0 i) (hp1 i)).1)
      (fun i => (regularizedGate_interior hδ0 hδ1 (hp0 i) (hp1 i)).2)
      v₀ v₁ v₂ ell h hv₀ hv₁ hv₂ hell hh hval hder hsecond hFδ hHδ
    simpa only [norm_gradient_eq_fderiv, norm_hessian_eq_second_fderiv] using hi.2.2
  have hc := regularizedMixture_continuous_derivatives q V hq hV x
  have hfirst := continuous_le_at_zero_of_Ioo hc.1 (fun δ hδ0 hδ1 => (hb δ hδ0 hδ1).1)
  have hlast := continuous_le_at_zero_of_Ioo hc.2 (fun δ hδ0 hδ1 => (hb δ hδ0 hδ1).2)
  refine ⟨contDiff_bernoulliMixture q V hq hV, ?_, ?_, ?_⟩
  · have he : bernoulliMixture q V x =
        pmfMean (bernoulliProduct (fun i => q i x) hp0 hp1) (fun w => V w x) := by
      simp only [bernoulliMixture, pmfMean, smul_eq_mul, ← bernoulliDensity_eq_toReal]
    rw [he]
    exact (abs_pmfMean_le _ _).trans (pmfMean_le_const _ v₀ hval)
  · simpa only [regularizedMixture_zero, norm_gradient_eq_fderiv] using hfirst
  · simpa only [regularizedMixture_zero, norm_hessian_eq_second_fderiv] using hlast

end
end SecondOrder
