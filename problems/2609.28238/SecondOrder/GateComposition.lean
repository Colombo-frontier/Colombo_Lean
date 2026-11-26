import SecondOrder.AffineGate
import SecondOrder.LocalHessian

namespace SecondOrder
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem scalarComposition_gradient {u : E → ℝ} {g : ℝ → ℝ} {g' : ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hg : HasDerivAt g g' (u x)) :
    gradient (g ∘ u) x = g' • gradient u x := by
  have he := (hg.comp_hasFDerivAt x hu.hasFDerivAt).fderiv
  simp only [gradient, he, map_smul]

theorem affineGate_gradient {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (s a : ℝ) :
    gradient (affineGate s a ∘ u) x = affineGateFirst s a (u x) • gradient u x :=
  scalarComposition_gradient hu (affineGate_hasDerivAt s a (u x))

/-- Actual Hessian chain rule, including the rank-one outer-product term. -/
theorem affineGate_hessian {u : E → ℝ} (hu : ContDiff ℝ 2 u) (s a : ℝ) (x : E) :
    fderiv ℝ (gradient (affineGate s a ∘ u)) x =
      affineGateFirst s a (u x) • fderiv ℝ (gradient u) x +
        (affineGateSecond s a (u x) • fderiv ℝ u x).smulRight (gradient u x) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hg : ContDiff ℝ 1 (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hu.fderiv_right (by norm_num))
  have he : gradient (affineGate s a ∘ u) = fun y => affineGateFirst s a (u y) • gradient u y :=
    funext (fun y => affineGate_gradient (hd y) s a)
  rw [he]
  exact (((affineGateFirst_hasDerivAt s a (u x)).comp_hasFDerivAt x (hd x).hasFDerivAt).smul
    ((hg.differentiable (by norm_num) x).hasFDerivAt)).fderiv

theorem affineGate_gradient_fisher {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (s a : ℝ) :
    ‖gradient (affineGate s a ∘ u) x‖^2 ≤
      1225*s^2*‖gradient u x‖^2*affineGate s a (u x)*(1-affineGate s a (u x)) := by
  have hf := mul_le_mul_of_nonneg_right (affineGate_fisher s a (u x)) (sq_nonneg ‖gradient u x‖)
  rw [deriv_affineGate] at hf
  rw [affineGate_gradient hu, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [hf]

theorem affineGate_gradient_fisher_bound {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (s a : ℝ) {B : ℝ} (hb : ‖gradient u x‖^2 ≤ B) :
    ‖gradient (affineGate s a ∘ u) x‖^2 ≤
      1225*s^2*B*affineGate s a (u x)*(1-affineGate s a (u x)) := by
  have hv := gate_mem_Icc (s*(u x-a))
  have hnonneg : 0 ≤ 1225*s^2*affineGate s a (u x)*(1-affineGate s a (u x)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) hv.1) (sub_nonneg.mpr hv.2)
  have hm := mul_le_mul_of_nonneg_left hb hnonneg
  nlinarith [affineGate_gradient_fisher hu s a]

theorem affineGateFirst_bound (s a x : ℝ) : ‖affineGateFirst s a x‖ ≤ |s| *140 := by
  rw [affineGateFirst, norm_mul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg s)
  simpa only [deriv_gate] using (gate_derivative_bounds (s*(x-a))).1

theorem affineGateSecond_bound (s a x : ℝ) : ‖affineGateSecond s a x‖ ≤ s^2*420 := by
  rw [affineGateSecond, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg s)
  simpa only [deriv_gate, deriv_gateFirst] using (gate_derivative_bounds (s*(x-a))).2.1

/-- This is the bound used for both completion gates in the lower-bound families. -/
theorem affineGate_hessian_bound {u : E → ℝ} (hu : ContDiff ℝ 2 u) (s a : ℝ) (x : E) :
    ‖fderiv ℝ (gradient (affineGate s a ∘ u)) x‖ ≤
      |s| *140*‖fderiv ℝ (gradient u) x‖+s^2*420*‖gradient u x‖^2 := by
  have hn : ‖fderiv ℝ u x‖ = ‖gradient u x‖ := by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  have hn2 : ‖affineGateSecond s a (u x) • fderiv ℝ u x‖ =
      ‖affineGateSecond s a (u x)‖*‖fderiv ℝ u x‖ :=
    norm_smul (affineGateSecond s a (u x)) (fderiv ℝ u x)
  rw [affineGate_hessian hu]
  calc
    _ ≤ ‖affineGateFirst s a (u x) • fderiv ℝ (gradient u) x‖+
        ‖(affineGateSecond s a (u x) • fderiv ℝ u x).smulRight (gradient u x)‖ := norm_add_le _ _
    _ = ‖affineGateFirst s a (u x)‖*‖fderiv ℝ (gradient u) x‖+
        ‖affineGateSecond s a (u x)‖*‖gradient u x‖^2 := by
      simp only [ContinuousLinearMap.norm_smulRight_apply, hn2, norm_smul, hn]
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (affineGateFirst_bound s a (u x)) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (affineGateSecond_bound s a (u x)) (sq_nonneg _))

/-- Flatness through second order remains valid even at the activation boundary. -/
theorem affineGate_composition_flat {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {s a : ℝ} (hs : 0 ≤ s) {x : E} (hx : u x ≤ a) :
    affineGate s a (u x) = 0 ∧ gradient (affineGate s a ∘ u) x = 0 ∧
      fderiv ℝ (gradient (affineGate s a ∘ u)) x = 0 := by
  have hf := affineGate_flat_left hs hx
  refine ⟨hf.1, ?_, ?_⟩
  · rw [affineGate_gradient (hu.differentiable (by norm_num) x), hf.2.1, zero_smul]
  · rw [affineGate_hessian hu, hf.2.1, hf.2.2.1]
    ext v
    simp

end
end SecondOrder
