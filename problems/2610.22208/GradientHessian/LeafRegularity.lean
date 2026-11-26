import GradientHessian.LeafDerivatives

/-! Global third derivative and Hessian-Lipschitz bounds of the actual leaf.
The full common quadratic has identically zero third derivative. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open scoped InnerProductSpace

section Quadratics
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem linear_higher_derivative_zero (L : F →L[ℝ] G) (n : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ (n+2) L x‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ => L := funext (fun _ => L.fderiv)
  rw [he]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]

theorem norm_square_third_zero (L : F →L[ℝ] G) (x : F) :
    iteratedFDeriv ℝ 3 (fun z => ‖L z‖^2) x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := (innerSL ℝ : G →L[ℝ] G →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (L.contDiff : ContDiff ℝ 3 L) (L.contDiff : ContDiff ℝ 3 L) x le_rfl (norm_innerSL_le ℝ)
  have he : (fun z => (innerSL ℝ : G →L[ℝ] G →L[ℝ] ℝ) (L z) (L z)) =
      (fun z => ‖L z‖^2) := by
    funext z
    exact real_inner_self_eq_norm_sq (L z)
  rw [he] at h
  simpa only [Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self,
    Nat.reduceSub, linear_higher_derivative_zero L 0 x, linear_higher_derivative_zero L 1 x,
    mul_zero, zero_mul, add_zero, zero_add] using h

theorem weighted_square_third_zero (c : ℝ) (L : F →L[ℝ] G) (x : F) :
    iteratedFDeriv ℝ 3 (fun z => c*‖L z‖^2) x = 0 := by
  have he : (fun z => c*‖L z‖^2) = c • (fun z => ‖L z‖^2) := rfl
  rw [he, iteratedFDeriv_const_smul_apply (L.contDiff.norm_sq ℝ).contDiffAt,
    norm_square_third_zero, smul_zero]

end Quadratics

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem publicQuadratic_third_zero (Z : Space Y E m) :
    iteratedFDeriv ℝ 3 (publicQuadratic m) Z = 0 := by
  have hX : iteratedFDeriv ℝ 3 (Inner.publicQuadratic (Y := Y) (E := E) m Inner.absoluteDepth) Z = 0 := by
    let f := fun (i : Fin m) (j : Fin (Inner.absoluteDepth+2)) (W : Space Y E m) =>
      (4/Inner.radius Inner.absoluteDepth j)*‖tasks Y E m (Inner.absoluteDepth+2) W i j‖^2
    have hf (i : Fin m) (j : Fin (Inner.absoluteDepth+2)) : ContDiff ℝ 3 (f i j) :=
      contDiff_const.mul (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (Inner.absoluteDepth+2) => E) j).contDiff.comp
        (Inner.taskProjection (Y := Y) (E := E) m Inner.absoluteDepth i).contDiff).norm_sq ℝ)
    change iteratedFDeriv ℝ 3 (fun W => ∑ i, ∑ j, f i j W) Z = 0
    rw [iteratedFDeriv_sum (f := fun i W => ∑ j, f i j W)
      (fun i _ => ContDiff.sum (fun j _ => hf i j))]
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [iteratedFDeriv_sum (fun j _ => hf i j)]
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    exact weighted_square_third_zero _
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (Inner.absoluteDepth+2) => E) j).comp
        (Inner.taskProjection (Y := Y) (E := E) m Inner.absoluteDepth i)) Z
  unfold publicQuadratic
  rw [iteratedFDeriv_add_apply'
    (contDiff_const.mul ((numerical Y E m (Inner.absoluteDepth+2)).contDiff.norm_sq ℝ)).contDiffAt
    (Inner.publicQuadratic_contDiff m Inner.absoluteDepth).contDiffAt,
    weighted_square_third_zero, hX, add_zero]

variable [CompleteSpace Y] [CompleteSpace E]

theorem objective_third_derivative_bound (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : ‖A‖ ≤ m)
    (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m) : ‖iteratedFDeriv ℝ 3 (objective A b a v) Z‖ ≤ leafJetConstant := by
  unfold objective
  rw [iteratedFDeriv_add_apply' (publicQuadratic_contDiff m).contDiffAt
    (correction_contDiff hm A b a v).contDiffAt, publicQuadratic_third_zero, zero_add]
  simpa only [Nat.sub_self, pow_zero, mul_one] using
    correction_derivative_bound hm A hA b a v hb ha hv Z (n := 3) le_rfl

theorem objective_hessian_lipschitz (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : ‖A‖ ≤ m)
    (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1) :
    LipschitzWith ⟨leafJetConstant, leafJetConstant_pos.le⟩ (iteratedFDeriv ℝ 2 (objective A b a v)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (((objective_contDiff hm A b a v).iteratedFDeriv_right (by norm_num : (1:WithTop ℕ∞)+2 ≤ 3)).differentiable
      (by norm_num))
  intro Z
  change ‖fderiv ℝ (iteratedFDeriv ℝ 2 (objective A b a v)) Z‖ ≤ leafJetConstant
  rw [norm_fderiv_iteratedFDeriv]
  exact objective_third_derivative_bound hm A hA b a v hb ha hv Z

end GradientHessian.Leaf
