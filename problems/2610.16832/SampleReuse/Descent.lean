import SampleReuse.Model
import SecondOrder.ActualProgress

open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_alignment {G g : E} {ε : ℝ} (hε : 0 < ε)
    (he : ‖g-G‖ ≤ ε/4) (hg : 3*ε/4 < ‖g‖) :
    ‖(‖g‖⁻¹ : ℝ) • g‖ = 1 ∧
      ε/2 ≤ ⟪G, (‖g‖⁻¹ : ℝ) • g⟫_ℝ := by
  have hp : 0 < ‖g‖ := by linarith
  have hn : ‖(‖g‖⁻¹ : ℝ) • g‖ = 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), ne_of_gt hp]
  refine ⟨hn, ?_⟩
  have hcs := real_inner_le_norm (g-G) ((‖g‖⁻¹ : ℝ) • g)
  rw [hn, mul_one, inner_sub_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hcs
  have hid : ‖g‖⁻¹ * ‖g‖^2 = ‖g‖ := by field_simp; ring
  rw [hid] at hcs
  linarith

/-- Equation (4.3): descent of the actual normalized gradient step. -/
theorem normalized_gradient_descent {f : E → ℝ} {G : E → E} {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε)
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x-G y‖ ≤ L*‖x-y‖) (x g : E)
    (he : ‖g-G x‖ ≤ ε/4) (hg : 3*ε/4 < ‖g‖) :
    f (x + (-(ε/(4*L))) • ((‖g‖⁻¹ : ℝ) • g))-f x ≤ -(3*ε^2/(32*L)) := by
  obtain ⟨hu, ha⟩ := normalized_alignment hε he hg
  let u := (‖g‖⁻¹ : ℝ) • g
  have hs : 0 ≤ ε/(4*L) := by positivity
  have hn : ‖(-(ε/(4*L))) • u‖ = ε/(4*L) := by
    simp [norm_smul, u, hu, Real.norm_eq_abs, abs_of_nonneg hs,
      abs_of_pos hε, abs_of_pos hL]
  have ht := (abs_le.mp (SecondOrder.smooth_remainder hd hLip x
    ((-(ε/(4*L))) • u))).2
  rw [real_inner_smul_right, hn] at ht
  have halign := mul_le_mul_of_nonneg_left ha hs
  have heq : -(ε/(4*L))*(ε/2) + L/2*(ε/(4*L))^2 = -(3*ε^2/(32*L)) := by
    field_simp
    ring
  rw [← heq]
  dsimp [u] at ht
  linarith

/-- The mean of the two actual signed curvature moves, using the full
Hessian-Lipschitz Taylor theorem. This is the conditional mean once a fresh
independent fair sign is supplied by the algorithm. -/
theorem signed_curvature_descent {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {L γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x, HasFDerivAt G (H x) x)
    (hH : ∀ x y, ‖H x-H y‖ ≤ L*‖x-y‖)
    (x v : E) (hv : ‖v‖ = 1) (hc : ⟪H x v,v⟫_ℝ ≤ -γ/2) :
    (f (x+(γ/L)•v) + f (x+(-(γ/L))•v))/2-f x ≤ -(γ^3/(12*L^2)) := by
  have hs : 0 ≤ γ/L := by positivity
  have hH' : ∀ x y, ‖H x-H y‖ ≤ L*‖x-y‖^(1:ℝ) := by
    simpa only [Real.rpow_one] using hH
  have hp := (abs_le.mp (SecondOrder.holder_taylor (by norm_num : (0:ℝ)<1)
    hf hG hH' x ((γ/L)•v))).2
  have hm := (abs_le.mp (SecondOrder.holder_taylor (by norm_num : (0:ℝ)<1)
    hf hG hH' x ((-(γ/L))•v))).2
  have hnp : ‖(γ/L)•v‖ = γ/L := by
    simp [norm_smul, hv, Real.norm_of_nonneg hs]
  have hnm : ‖(-(γ/L))•v‖ = γ/L := by
    simp [norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hs,
      abs_of_pos hγ, abs_of_pos hL]
  rw [hnp] at hp
  rw [hnm] at hm
  norm_num only at hp hm
  rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast] at hp hm
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hp hm
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (γ/L))
  have heq : (-γ/4)*(γ/L)^2 + L/6*(γ/L)^3 = -(γ^3/(12*L^2)) := by
    field_simp
    ring
  rw [← heq]
  nlinarith only [hp, hm, hh]

section ActualLoss
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
  {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.population_derivative (h : Admissible μ P f F x₀) (x : Point d) :
    HasFDerivAt f (innerSL ℝ (gradient f x)) x :=
  ((h.population_smooth.differentiable (by norm_num)) x).hasGradientAt.hasFDerivAt

theorem Admissible.normalized_gradient_descent (h : Admissible μ P f F x₀)
    (x g : Point d) {ε : ℝ} (hε : 0 < ε)
    (he : ‖g-gradient f x‖ ≤ ε/4) (hg : 3*ε/4 < ‖g‖) :
    f (x + (-(ε/(4*P.gradientLip))) • ((‖g‖⁻¹ : ℝ) • g))-f x ≤
      -(3*ε^2/(32*P.gradientLip)) :=
  SampleReuse.normalized_gradient_descent P.gradientLip_pos hε
    h.population_derivative h.population_gradient_lipschitz x g he hg

/-- Actual expectation over a fresh independent fair sign, conditional on a
fixed current point and direction. All derivatives come from the model. -/
theorem Admissible.signed_curvature_descent (h : Admissible μ P f F x₀)
    (x v : Point d) {γ : ℝ} (hγ : 0 < γ) (hv : ‖v‖ = 1)
    (hc : ⟪hessian f x v,v⟫_ℝ ≤ -γ/2) :
    (∫ b, f (SecondOrder.curvatureNext (γ/P.hessianLip) x v b)
      ∂(PMF.uniformOfFintype Bool).toMeasure)-f x ≤ -(γ^3/(12*P.hessianLip^2)) := by
  rw [SecondOrder.curvatureNext_mean]
  exact SampleReuse.signed_curvature_descent P.hessianLip_pos hγ
    h.population_derivative (SecondOrder.gradient_has_hessian h.population_smooth)
    h.population_hessian_lipschitz x v hv hc

end ActualLoss

end
end SampleReuse
