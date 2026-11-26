import Nonsmooth.RadialQuadraticCalculus
import Nonsmooth.SoftVectorPotentialClass
import Nonsmooth.AffineBallConstraints

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ballPolytopeConstraint_radial_representation (c : E) (R : ℝ)
    (a : ι → E) (b : ι → ℝ) (j : Option ι) :
    ∃ (q : ℝ) (v : E) (d : ℝ), 0 ≤ q ∧ ∀ x,
      ballPolytopeConstraint c R a b j x = radialQuadratic q v d x := by
  classical
  cases j with
  | none =>
    refine ⟨1, (-2 : ℝ) • c, ‖c‖ ^ 2 - R ^ 2, by norm_num, ?_⟩
    intro x
    simp only [ballPolytopeConstraint, radialQuadratic, norm_sub_sq_real,
      real_inner_smul_left, one_mul, real_inner_comm x c]
    ring
  | some j =>
    by_cases ha : a j = 0
    · refine ⟨0, 0, (if 0 ≤ b j then -1 else 1), by norm_num, ?_⟩
      intro x
      simp only [ballPolytopeConstraint, affineSoftConstraint, if_pos ha, radialQuadratic,
        zero_mul, inner_zero_left, zero_add]
    · refine ⟨0, a j, -b j, by norm_num, ?_⟩
      intro x
      simp only [ballPolytopeConstraint, affineSoftConstraint, if_neg ha, radialQuadratic,
        zero_mul, zero_add, sub_eq_add_neg]

theorem scaled_ballPolytopeConstraint_radial_representation (c : E) (R : ℝ)
    (a : ι → E) (b : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) (j : Option ι) :
    ∃ (q : ℝ) (v : E) (d : ℝ), 0 ≤ q ∧ ∀ x,
      r * ballPolytopeConstraint c R a b j x = radialQuadratic q v d x := by
  obtain ⟨q, v, d, hq, he⟩ := ballPolytopeConstraint_radial_representation c R a b j
  refine ⟨r * q, r • v, r * d, mul_nonneg hr hq, ?_⟩
  intro x
  rw [he, radialQuadratic_smul]

theorem radialQuadratic_soft_potential_class [Fintype ι] {ρ : ℝ} (hρ : 0 < ρ)
    (q : ι → ℝ) (b : ι → E) (c : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    C2StrongQuadraticPotential (softVectorPotential ρ (fun i => radialQuadratic (q i) (b i) (c i))) ρ := by
  apply softVectorPotential_c2StrongQuadratic hρ _
    (fun i => radialQuadraticScore (q i) (b i))
    (fun i _ => (2 * q i) • realInnerBilinear (E := E))
    (fun i => radialQuadratic_contDiff (q i) (b i) (c i))
    (fun i => radialQuadratic_hasFDerivAt (q i) (b i) (c i))
    (fun i => radialQuadraticScore_hasFDerivAt (q i) (b i))
    (fun i _ => radialQuadratic_hessian_symmetric (q i))
    (fun i _ => radialQuadratic_hessian_nonnegative (hq i))
    (fun i => |q i| + ‖b i‖ + |c i|)
    (fun i => ‖(2 * q i) • realInnerBilinear (E := E)‖)
    (fun i => by positivity)
    (fun i => norm_nonneg ((2 * q i) • realInnerBilinear (E := E)))
    (fun i => radialQuadratic_abs_bound (q i) (b i) (c i))
  exact fun _ _ => le_refl _

/-- The actual soft Gaussian ball/polytope potentials satisfy every
primitive hypothesis of the finite repeated-integration theorem,
including the explicitly checked Hessian symmetry. -/
theorem gaussianBallPolytopePotential_c2Strong [Fintype ι] {ρ : ℝ} (hρ : 0 < ρ)
    (c : E) (R : ℝ) (a : ι → E) (b : ι → ℝ) (n : ℕ) :
    C2StrongQuadraticPotential
      (fun x : E => ρ / 2 * ‖x‖ ^ 2 + softInequalityPenalty (ballPolytopeConstraint c R a b) n x) ρ := by
  classical
  choose q v d hq he using (fun j => scaled_ballPolytopeConstraint_radial_representation
    c R a b (Nat.cast_nonneg n) j)
  have hf : (fun j x => (n : ℝ) * ballPolytopeConstraint c R a b j x) =
      (fun j => radialQuadratic (q j) (v j) (d j)) := by
    funext j x
    exact he j x
  change C2StrongQuadraticPotential
    (softVectorPotential ρ (fun j x => (n : ℝ) * ballPolytopeConstraint c R a b j x)) ρ
  rw [hf]
  exact radialQuadratic_soft_potential_class hρ q v d hq

theorem strictGaussianBallPolytopePotential_c2Strong [Fintype ι]
    (c : E) (R : ℝ) (a : ι → E) (b : ι → ℝ) (n : ℕ) :
    C2StrongQuadraticPotential
      (fun x : E => (1 + 2 / ((n : ℝ) + 1)) / 2 * ‖x‖ ^ 2 +
        softInequalityPenalty (ballPolytopeConstraint c R a b) n x)
      (1 + 2 / ((n : ℝ) + 1)) :=
  gaussianBallPolytopePotential_c2Strong (by positivity) c R a b n

end
end Nonsmooth
