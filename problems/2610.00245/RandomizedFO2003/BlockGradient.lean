import RandomizedFO2003.CascadeForcing
import RandomizedFO2003.RadialGate

namespace RandomizedFO2003.Cascade

open Primitives Calculus InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def quadratic (A : E →L[ℝ] E) (x : E) : ℝ :=
  (1 / 2 : ℝ) * inner (𝕜 := ℝ) x (A x)

omit [CompleteSpace E] in
theorem quadratic_contDiff (A : E →L[ℝ] E) (n : ℕ) : ContDiff ℝ n (quadratic A) :=
  contDiff_const.mul (contDiff_id.inner ℝ A.contDiff)

theorem quadratic_hasGradientAt (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    HasGradientAt (quadratic A) (A x) x := by
  apply hasGradientAt_of_pairing (((hasFDerivAt_id x).inner ℝ A.hasFDerivAt).const_mul (1 / 2 : ℝ))
  intro v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, id_eq]
  rw [← A.adjoint_inner_left v x, hA.adjoint_eq, real_inner_comm v (A x)]
  ring

theorem radialReadout_hasGradientAt (a : E) (B α : ℝ) (x : E) :
    HasGradientAt (radialReadout a B α)
      (α⁻¹ • (fderiv ℝ (radialSquash B : E → E) x).adjoint a) x := by
  have hR := ((radialSquash_contDiff B 1).differentiable (by norm_num) x).hasFDerivAt
  apply hasGradientAt_of_pairing ((forcingReadout_hasFDerivAt a α (radialSquash B x)).comp x hR)
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem radialGate_hasGradientAt (a : E) (B α : ℝ) (x : E) :
    HasGradientAt (radialGate a B α)
      ((deriv gate (radialReadout a B α x) / α) •
        (fderiv ℝ (radialSquash B : E → E) x).adjoint a) x := by
  have hg := ((gate_contDiff 1).differentiable (by norm_num) (radialReadout a B α x)).hasDerivAt
  apply hasGradientAt_of_pairing (hg.comp_hasFDerivAt x (radialReadout_hasGradientAt a B α x).hasFDerivAt)
  intro v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, toDual_apply, real_inner_smul_left]
  rw [div_eq_mul_inv]
  ring

theorem radialGate_gradient (a : E) (B α : ℝ) (x : E) :
    gradient (radialGate a B α) x = (deriv gate (radialReadout a B α x) / α) •
      (fderiv ℝ (radialSquash B : E → E) x).adjoint a :=
  (radialGate_hasGradientAt a B α x).gradient

theorem radialGate_gradient_identity_region (a : E) {B : ℝ} (hB : 0 < B) (α : ℝ) {x : E}
    (hx : ‖x‖ ≤ B) : gradient (radialGate a B α) x =
      (deriv gate (inner (𝕜 := ℝ) a x / α) / α) • a := by
  rw [radialGate_gradient, radialSquash_fderiv_eq_id hB hx]
  simp only [radialReadout, radialSquash_eq_self hB hx, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply]

/-- Holding neighboring blocks fixed gives exactly this one-variable
potential, up to an additive constant. -/
noncomputable def blockPotential (A : E →L[ℝ] E) (a b : E)
    (B α D C₀ K c out : ℝ) (x : E) : ℝ :=
  quadratic A x - c * forcing b D C₀ K x - out * radialGate a B α x

omit [CompleteSpace E] in
theorem blockPotential_contDiff (A : E →L[ℝ] E) (a b : E)
    (B α D C₀ K c out : ℝ) (n : ℕ) : ContDiff ℝ n (blockPotential A a b B α D C₀ K c out) :=
  ((quadratic_contDiff A n).sub (contDiff_const.mul (forcing_contDiff b D C₀ K n))).sub
    (contDiff_const.mul (radialGate_contDiff a B α n))

theorem blockPotential_hasGradientAt (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (a b : E)
    (B α : ℝ) {D : ℝ} (hD : D ≠ 0) (C₀ K c out : ℝ) (x : E) :
    HasGradientAt (blockPotential A a b B α D C₀ K c out)
      (A x - (c * saturationSlope K (forcingReadout b D x)) • b -
        (out * deriv gate (radialReadout a B α x) / α) •
          (fderiv ℝ (radialSquash B : E → E) x).adjoint a) x := by
  have h := hasGradientAt_sub
    (hasGradientAt_sub (quadratic_hasGradientAt A hA x)
      (hasGradientAt_const_mul (forcing_hasGradientAt b hD C₀ K x) c))
    (hasGradientAt_const_mul (radialGate_hasGradientAt a B α x) out)
  simpa only [smul_smul, ← mul_div_assoc] using h

theorem blockPotential_gradient_identity_region (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (a b : E)
    {B : ℝ} (hB : 0 < B) (α : ℝ) {D : ℝ} (hD : D ≠ 0) (C₀ K c out : ℝ) {x : E}
    (hx : ‖x‖ ≤ B) :
    gradient (blockPotential A a b B α D C₀ K c out) x =
      A x - (c * saturationSlope K (forcingReadout b D x)) • b -
        (out * deriv gate (inner (𝕜 := ℝ) a x / α) / α) • a := by
  rw [(blockPotential_hasGradientAt A hA a b B α hD C₀ K c out x).gradient,
    radialSquash_fderiv_eq_id hB hx]
  simp only [radialReadout, radialSquash_eq_self hB hx, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply]

end RandomizedFO2003.Cascade
