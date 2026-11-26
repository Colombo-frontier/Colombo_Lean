import GradientHessian.LeafLocalization

/-! Explicit one-product factorization. These identities concern known
marked coefficients; they do not disclose any hidden mark or matrix. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

def valueFromProduct (M L : ℝ) (y t : Y) : ℝ :=
  M*‖y‖^2 + (1/2)*LeafCutoff.cutoff L y*⟪y,t-(2*M) • y⟫_ℝ

def gradientFromProduct (M L : ℝ) (y t : Y) : Y :=
  (2*M) • y + LeafCutoff.cutoff L y • (t-(2*M) • y) +
    (deriv (LeafCutoff.radial L) ‖y‖/(2*‖y‖)*⟪y,t-(2*M) • y⟫_ℝ) • y

theorem base_eq_valueFromProduct (M L : ℝ) (A : Y →L[ℝ] Y) (y : Y) :
    LeafNumerical.base M L A y = valueFromProduct M L y (A y) := rfl

theorem matrix_eq_gradientFromProduct (M L : ℝ) (A : Y →L[ℝ] Y) (y : Y) :
    LeafNumerical.gradientMatrix M L A y y = gradientFromProduct M L y (A y) := rfl

theorem objective_one_product (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    objective A b a v Z =
      valueFromProduct m (capRadius m) (numerical Y E m (Inner.absoluteDepth+2) Z)
        (A (numerical Y E m (Inner.absoluteDepth+2) Z)) +
      Inner.publicQuadratic m Inner.absoluteDepth Z + Inner.residual b a v Z :=
  objective_decomposition A b a v Z

variable [CompleteSpace Y]

theorem numerical_gradient_one_product (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    gradient (fun y => objective A b a v (replaceNumerical Z y))
      (numerical Y E m (Inner.absoluteDepth+2) Z) =
      gradientFromProduct m (capRadius m) (numerical Y E m (Inner.absoluteDepth+2) Z)
        (A (numerical Y E m (Inner.absoluteDepth+2) Z)) + numericalForce b a v Z :=
  (objective_numerical_hasGradientAt hm A hsym b a v Z).gradient

omit [CompleteSpace Y] in
/-- The numerical Hessian is the derivative of the explicit known-matrix
formula plus the marked residual Hessian; the public memory constant vanishes. -/
theorem numerical_hessian_from_matrix (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) (y : Y) :
    iteratedFDeriv ℝ 2 (fun z => objective A b a v (replaceNumerical Z z)) y =
      iteratedFDeriv ℝ 2 (fun z => valueFromProduct m (capRadius m) z (A z)) y +
      iteratedFDeriv ℝ 2 (fun z => Inner.residual b a v (replaceNumerical Z z)) y := by
  have he : (fun z => objective A b a v (replaceNumerical Z z)) =
      (fun z => (valueFromProduct m (capRadius m) z (A z) +
        Inner.residual b a v (replaceNumerical Z z)) + Inner.publicQuadratic m Inner.absoluteDepth Z) := by
    funext z
    simp only [objective_one_product, numerical_replaceNumerical, Inner.publicQuadratic, tasks_replaceNumerical]
    ring
  have hv : ContDiff ℝ 3 (fun z => valueFromProduct m (capRadius m) z (A z)) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add
      (LeafCorrection.correction_contDiff (capRadius_pos hm) (LeafNumerical.deviation m A))
  have hr := (Inner.residual_contDiff b a v).comp (replaceNumerical_contDiff Z)
  dsimp only [Function.comp_def] at hr
  rw [he, iteratedFDeriv_add_apply' ((hv.add hr).contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3))
      (contDiffAt_const : ContDiffAt ℝ (2:ℕ) (fun _ : Y => Inner.publicQuadratic m Inner.absoluteDepth Z) y),
    iteratedFDeriv_succ_const, Pi.zero_apply, add_zero,
    iteratedFDeriv_add_apply' (hv.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)) (hr.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3))]

end GradientHessian.Leaf
