import SecondOrder.ConservativeUnbiased
import SecondOrder.CurvaturePayloadBounds

namespace SecondOrder
noncomputable section
variable {T : ℕ} {E : Fin (T+1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

theorem dependentBlockProj_norm_le_one (i : Fin (T+1)) :
    ‖dependentBlockProj (E := E) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul,dependentBlockProj_apply] using PiLp.norm_apply_le x i

theorem conservativePayload_bounds (W S : (i : Fin (T+1)) → E i → ℝ)
    (hW : ∀ i, ContDiff ℝ 2 (W i)) (hS : ∀ i, ContDiff ℝ 2 (S i)) (x : PiLp 2 E)
    (v₀ v₁ v₂ : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hval : ∀ i, |S i (x i)-W i (x i)| ≤ v₀)
    (hder : ∀ i, ‖gradient (fun y => S i y-W i y) (x i)‖ ≤ v₁)
    (hH : ∀ i, ‖fderiv ℝ (gradient (fun y => S i y-W i y)) (x i)‖ ≤ v₂) (j : ℕ) :
    |conservativePayload W S j x| ≤ 2*v₀ ∧
      ‖gradient (conservativePayload W S j) x‖ ≤ 2*v₁ ∧
      ‖fderiv ℝ (gradient (conservativePayload W S j)) x‖ ≤ 2*v₂ := by
  letI : NormedSpace ℝ (PiLp 2 E) := inferInstance
  by_cases hj : j<T+1
  · let i : Fin (T+1) := ⟨j,hj⟩
    let n : E i → ℝ := fun y => S i y-W i y
    let f : PiLp 2 E → ℝ := n ∘ dependentBlockProj i
    have hn : ContDiff ℝ 2 n := (hS i).sub (hW i)
    have hf : ContDiff ℝ 2 f := hn.comp (dependentBlockProj (E := E) i).contDiff
    have he : conservativePayload W S j=fun y => curvaturePayloadScale j*f y := by
      funext y
      simp only [conservativePayload,dif_pos hj]
      rfl
    have hs := curvaturePayloadScale_bounds j
    have hg : ‖gradient f x‖ ≤ v₁ :=
      (gradient_linear_contraction n hn (dependentBlockProj i) (dependentBlockProj_norm_le_one i) x).trans (hder i)
    have hh : ‖fderiv ℝ (gradient f) x‖ ≤ v₂ :=
      (hessian_linear_contraction n hn (dependentBlockProj i) (dependentBlockProj_norm_le_one i) x).trans (hH i)
    rw [he]
    refine ⟨?_,?_,?_⟩
    · rw [abs_mul,abs_of_nonneg hs.1]
      exact mul_le_mul hs.2 (hval i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    · rw [gradient_const_mul_scalar (hf.differentiable (by norm_num)),norm_smul,
        Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact mul_le_mul hs.2 hg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    · rw [hessian_const_mul_scalar hf,
        norm_smul (curvaturePayloadScale j) (fderiv ℝ (gradient f) x),Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact mul_le_mul hs.2 hh (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  · have he : conservativePayload W S j=fun _ => (0:ℝ) := by
      funext y
      simp only [conservativePayload,dif_neg hj]
    have hg : gradient (fun _ : PiLp 2 E => (0:ℝ))=fun _ => 0 := by
      funext y
      simp only [gradient,fderiv_const,Pi.zero_apply,map_zero]
    rw [he]
    simp only [hg,fderiv_const,Pi.zero_apply,norm_zero,abs_zero]
    exact ⟨by positivity,by positivity,by positivity⟩

/-- The value, gradient, and Hessian errors in the general conservative
embedding have exactly the selector constants for payload bounds 2v.
No factor depending on the chain length or any block dimension occurs. -/
theorem conservativeChain_error_bounds (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ)
    (hreg : ContDiff ℝ 2 reg) (hW : ∀ i, ContDiff ℝ 2 (W i))
    (hS : ∀ i, ContDiff ℝ 2 (S i)) (hp : ∀ i, ContDiff ℝ 2 (p i)) (x : PiLp 2 E)
    (hp0 : ∀ i, 0 ≤ p i (x i)) (hp1 : ∀ i, p i (x i) ≤ 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ i, |S i (x i)-W i (x i)| ≤ v₀)
    (hder : ∀ i, ‖gradient (fun y => S i y-W i y) (x i)‖ ≤ v₁)
    (hsecond : ∀ i, ‖fderiv ℝ (gradient (fun y => S i y-W i y)) (x i)‖ ≤ v₂)
    (hF : ∀ i, ‖gradient (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (gradient (p i)) (x i)‖ ≤ h) :
    let F := conservativePopulation reg W p
    ContDiff ℝ 2 (conservativeChain reg W S p) ∧
      |conservativeChain reg W S p x-F x| ≤ 2*v₀ ∧
      ‖gradient (conservativeChain reg W S p) x-gradient F x‖ ≤ 2*v₁+2*v₀*ell ∧
      ‖fderiv ℝ (gradient (conservativeChain reg W S p)) x-fderiv ℝ (gradient F) x‖ ≤
        2*v₂+4*v₁*ell+4*v₀*(h+ell^2) := by
  have hb := conservativePayload_bounds W S hW hS x v₀ v₁ v₂ hv₀ hv₁ hv₂ hval hder hsecond
  have he := dependentConservativeLoss_error_bounds (conservativePopulation reg W p) p
    (fun _ : Unit => conservativePayload W S) ()
    (conservativePopulation_contDiff reg W p hreg hW hp) hp
    (fun j _ => conservativePayload_contDiff W S hW hS j) x hp0 hp1
    (2*v₀) (2*v₁) (2*v₂) ell h (by positivity) (by positivity) (by positivity) hell hh
    (fun j _ => (hb j).1) (fun j _ => (hb j).2.1) (fun j _ => (hb j).2.2) hF hH
  simpa only [show 2*(2*v₁)=4*v₁ by ring,show 2*(2*v₀)=4*v₀ by ring] using he

end
end SecondOrder
