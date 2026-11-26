import SecondOrder.FirstOrderGeometry

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

/-- The population F in the manuscript, including its output scale A. -/
def firstOrderScaledChain (Θ : Fin (T+1) → Fin d → Bool) (A : ℝ) (x : FirstOrderSpace d T) : ℝ :=
  A*firstOrderChain Θ x

theorem firstOrderScaledChain_contDiff (Θ : Fin (T+1) → Fin d → Bool) (A : ℝ) :
    ContDiff ℝ 3 (firstOrderScaledChain Θ A) := contDiff_const.mul (firstOrderChain_contDiff Θ)

theorem firstOrderScaledChain_gradient (Θ : Fin (T+1) → Fin d → Bool) (A : ℝ) :
    gradient (firstOrderScaledChain Θ A)=fun x => A • gradient (firstOrderChain Θ) x :=
  gradient_const_mul_scalar ((firstOrderChain_contDiff Θ).differentiable (by norm_num)) A

theorem firstOrderScaledChain_hessian (Θ : Fin (T+1) → Fin d → Bool) (A : ℝ) (x : FirstOrderSpace d T) :
    fderiv ℝ (gradient (firstOrderScaledChain Θ A)) x=A • fderiv ℝ (gradient (firstOrderChain Θ)) x :=
  hessian_const_mul_scalar ((firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)) A x

theorem firstOrderScaledChain_lower (Θ : Fin (T+1) → Fin d → Bool) {A : ℝ} (hA : 0≤A)
    (x : FirstOrderSpace d T) : -20*A*(T+1:ℕ)≤firstOrderScaledChain Θ A x := by
  have hh := mul_le_mul_of_nonneg_left (firstOrderChain_lower Θ x) hA
  convert hh using 1 <;> (try unfold firstOrderScaledChain) <;> ring

theorem firstOrderScaledChain_initial_gap (Θ : Fin (T+1) → Fin d → Bool) {A : ℝ} (hA : 0≤A)
    (x : FirstOrderSpace d T) : firstOrderScaledChain Θ A 0-firstOrderScaledChain Θ A x≤20*A*(T+1:ℕ) := by
  have hh := mul_le_mul_of_nonneg_left (firstOrderChain_initial_gap Θ x) hA
  convert hh using 1 <;> (try unfold firstOrderScaledChain) <;> ring

theorem firstOrderScaledChain_bddBelow (Θ : Fin (T+1) → Fin d → Bool) {A : ℝ} (hA : 0≤A) :
    BddBelow (Set.range (firstOrderScaledChain Θ A)) := by
  refine ⟨-20*A*(T+1:ℕ),?_⟩
  rintro z ⟨x,rfl⟩
  exact firstOrderScaledChain_lower Θ hA x

theorem firstOrderScaledChain_gap_inf (Θ : Fin (T+1) → Fin d → Bool) {A : ℝ} (hA : 0≤A) :
    firstOrderScaledChain Θ A 0-sInf (Set.range (firstOrderScaledChain Θ A))≤20*A*(T+1:ℕ) := by
  have hh : firstOrderScaledChain Θ A 0-20*A*(T+1:ℕ)≤sInf (Set.range (firstOrderScaledChain Θ A)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro z ⟨x,rfl⟩
    linarith [firstOrderScaledChain_initial_gap Θ hA x]
  linarith

theorem firstOrderScaledChain_gradient_lipschitz (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    {A : ℝ} (hA : 0≤A) (x y : FirstOrderSpace d T) :
    ‖gradient (firstOrderScaledChain Θ A) y-gradient (firstOrderScaledChain Θ A) x‖≤
      (firstOrderGeometryConstant*A)*‖y-x‖ := by
  rw [firstOrderScaledChain_gradient,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hA]
  exact (mul_le_mul_of_nonneg_left (firstOrderChain_gradient_lipschitz Θ hd x y) hA).trans_eq (by ring)

theorem firstOrderScaledChain_hessian_lipschitz (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    {A : ℝ} (hA : 0≤A) (x y : FirstOrderSpace d T) :
    ‖fderiv ℝ (gradient (firstOrderScaledChain Θ A)) y-fderiv ℝ (gradient (firstOrderScaledChain Θ A)) x‖≤
      (firstOrderGeometryConstant*A*Real.sqrt d)*‖y-x‖ := by
  rw [firstOrderScaledChain_hessian,firstOrderScaledChain_hessian,
    ←smul_sub A (fderiv ℝ (gradient (firstOrderChain Θ)) y) (fderiv ℝ (gradient (firstOrderChain Θ)) x),
    norm_smul A (fderiv ℝ (gradient (firstOrderChain Θ)) y-fderiv ℝ (gradient (firstOrderChain Θ)) x),
    Real.norm_eq_abs,abs_of_nonneg hA]
  exact (mul_le_mul_of_nonneg_left (firstOrderChain_hessian_lipschitz Θ hd x y) hA).trans_eq (by ring)

theorem firstOrderScaledChain_gradient_lower (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    {A : ℝ} (hA : 0≤A) (x : FirstOrderSpace d T)
    (hx : ∃ j, firstOrderBlockEncoding (Θ j) (x j)≤1/2) :
    firstOrderGradientConstant*A≤‖gradient (firstOrderScaledChain Θ A) x‖ := by
  rw [firstOrderScaledChain_gradient,norm_smul,Real.norm_eq_abs,abs_of_nonneg hA]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (firstOrderChain_gradient_lower Θ hd x hx) hA

/-- The first-order geometry lemma in the manuscript's scaled variables,
including the gap above the actual infimum. -/
theorem firstOrderScaledChain_geometry (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    {A : ℝ} (hA : 0≤A) :
    BddBelow (Set.range (firstOrderScaledChain Θ A)) ∧
    firstOrderScaledChain Θ A 0-sInf (Set.range (firstOrderScaledChain Θ A))≤20*A*(T+1:ℕ) ∧
    (∀ x y, ‖gradient (firstOrderScaledChain Θ A) y-gradient (firstOrderScaledChain Θ A) x‖≤
      (firstOrderGeometryConstant*A)*‖y-x‖) ∧
    (∀ x y, ‖fderiv ℝ (gradient (firstOrderScaledChain Θ A)) y-fderiv ℝ (gradient (firstOrderScaledChain Θ A)) x‖≤
      (firstOrderGeometryConstant*A*Real.sqrt d)*‖y-x‖) ∧
    (∀ x, (∃ j, firstOrderBlockEncoding (Θ j) (x j)≤1/2) →
      firstOrderGradientConstant*A≤‖gradient (firstOrderScaledChain Θ A) x‖) :=
  ⟨firstOrderScaledChain_bddBelow Θ hA,firstOrderScaledChain_gap_inf Θ hA,
    firstOrderScaledChain_gradient_lipschitz Θ hd hA,firstOrderScaledChain_hessian_lipschitz Θ hd hA,
    firstOrderScaledChain_gradient_lower Θ hd hA⟩

end
end SecondOrder
