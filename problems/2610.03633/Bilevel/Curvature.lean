import Bilevel.ModelBridge
import Bilevel.ResponseExistence
import Bilevel.HypergradientFormula

/-!
# Universal hypergradient curvature bound

Operator inverse differences and composition estimates retain the full
coefficient needed for the article's universal Lipschitz bound.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.Curvature

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Resolvent identity with the precise one-sided certificates used by the proof. -/
theorem inverse_difference (H₁ H₂ J₁ J₂ : E →L[ℝ] E)
    (hl : ∀ v, J₁ (H₁ v) = v) (hr : ∀ v, H₂ (J₂ v) = v) :
    J₁ - J₂ = J₁.comp ((H₂ - H₁).comp J₂) := by
  ext v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub, hl, hr]

theorem inverse_difference_norm (H₁ H₂ J₁ J₂ : E →L[ℝ] E)
    (hl : ∀ v, J₁ (H₁ v) = v) (hr : ∀ v, H₂ (J₂ v) = v)
    {μ : ℝ} (hμ : 0 < μ) (hJ₁ : ‖J₁‖ ≤ μ⁻¹) (hJ₂ : ‖J₂‖ ≤ μ⁻¹) :
    ‖J₁ - J₂‖ ≤ μ⁻¹ ^ 2 * ‖H₁ - H₂‖ := by
  rw [inverse_difference H₁ H₂ J₁ J₂ hl hr]
  calc
    ‖J₁.comp ((H₂ - H₁).comp J₂)‖ ≤ ‖J₁‖ * (‖H₂ - H₁‖ * ‖J₂‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ μ⁻¹ * (‖H₂ - H₁‖ * μ⁻¹) := by gcongr
    _ = μ⁻¹ ^ 2 * ‖H₁ - H₂‖ := by rw [norm_sub_rev H₂ H₁]; ring

/-- Difference of the two inverse-Hessian sensitivity maps. -/
theorem sensitivity_difference_norm (B₁ B₂ : E →L[ℝ] F) (H₁ H₂ J₁ J₂ : E →L[ℝ] E)
    (hl : ∀ v, J₁ (H₁ v) = v) (hr : ∀ v, H₂ (J₂ v) = v)
    {μ L ρ D : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hJ₁ : ‖J₁‖ ≤ μ⁻¹) (hJ₂ : ‖J₂‖ ≤ μ⁻¹) (hB₂ : ‖B₂‖ ≤ L)
    (hBdiff : ‖B₁ - B₂‖ ≤ ρ * D) (hHdiff : ‖H₁ - H₂‖ ≤ ρ * D) :
    ‖B₁.comp J₁ - B₂.comp J₂‖ ≤ ((1 + L / μ) * ρ / μ) * D := by
  have heq : B₁.comp J₁ - B₂.comp J₂ = (B₁ - B₂).comp J₁ + B₂.comp (J₁ - J₂) := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [heq]
  calc
    ‖(B₁ - B₂).comp J₁ + B₂.comp (J₁ - J₂)‖ ≤
        ‖(B₁ - B₂).comp J₁‖ + ‖B₂.comp (J₁ - J₂)‖ := norm_add_le _ _
    _ ≤ ‖B₁ - B₂‖ * ‖J₁‖ + ‖B₂‖ * ‖J₁ - J₂‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (ρ * D) * μ⁻¹ + L * (μ⁻¹ ^ 2 * (ρ * D)) := by
      have hi := inverse_difference_norm H₁ H₂ J₁ J₂ hl hr hμ hJ₁ hJ₂
      gcongr
      exact hi.trans (mul_le_mul_of_nonneg_left hHdiff (sq_nonneg _))
    _ = ((1 + L / μ) * ρ / μ) * D := by ring

/-- Hypergradient comparison at two points with distance budget `D`. -/
theorem hypergradient_difference (fx₁ fx₂ : F) (a₁ a₂ : E)
    (B₁ B₂ : E →L[ℝ] F) (H₁ H₂ J₁ J₂ : E →L[ℝ] E)
    (hl : ∀ v, J₁ (H₁ v) = v) (hr : ∀ v, H₂ (J₂ v) = v)
    {μ L Lf C ρ D : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hJ₁ : ‖J₁‖ ≤ μ⁻¹) (hJ₂ : ‖J₂‖ ≤ μ⁻¹)
    (hB₁ : ‖B₁‖ ≤ L) (hB₂ : ‖B₂‖ ≤ L)
    (hBdiff : ‖B₁ - B₂‖ ≤ ρ * D) (hHdiff : ‖H₁ - H₂‖ ≤ ρ * D)
    (hfx : ‖fx₁ - fx₂‖ ≤ Lf * D) (ha : ‖a₁ - a₂‖ ≤ Lf * D) (ha₂ : ‖a₂‖ ≤ C) :
    ‖(fx₁ - B₁ (J₁ a₁)) - (fx₂ - B₂ (J₂ a₂))‖ ≤
      ((1 + L / μ) * (Lf + ρ * C / μ)) * D := by
  have heq : (fx₁ - B₁ (J₁ a₁)) - (fx₂ - B₂ (J₂ a₂)) =
      (fx₁ - fx₂) - ((B₁.comp J₁) (a₁ - a₂) + (B₁.comp J₁ - B₂.comp J₂) a₂) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    abel
  have hs := sensitivity_difference_norm B₁ B₂ H₁ H₂ J₁ J₂ hl hr hμ hL hρ hD
    hJ₁ hJ₂ hB₂ hBdiff hHdiff
  have hb : ‖B₁.comp J₁‖ ≤ L * μ⁻¹ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
  rw [heq]
  calc
    ‖(fx₁ - fx₂) - ((B₁.comp J₁) (a₁ - a₂) + (B₁.comp J₁ - B₂.comp J₂) a₂)‖ ≤
        ‖fx₁ - fx₂‖ + (‖(B₁.comp J₁) (a₁ - a₂)‖ + ‖(B₁.comp J₁ - B₂.comp J₂) a₂‖) :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖fx₁ - fx₂‖ + (‖B₁.comp J₁‖ * ‖a₁ - a₂‖ + ‖B₁.comp J₁ - B₂.comp J₂‖ * ‖a₂‖) :=
      add_le_add_left (add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)) _
    _ ≤ Lf * D + ((L * μ⁻¹) * (Lf * D) + (((1 + L / μ) * ρ / μ) * D) * C) := by gcongr
    _ = ((1 + L / μ) * (Lf + ρ * C / μ)) * D := by ring

end Bilevel.Curvature

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem response_joint_distance (r : P.Response) (x z : X) :
    jointDistance x z (r.y x) (r.y z) ≤ (1 + Lg / μ) * ‖x - z‖ := by
  have hk : 0 ≤ Lg / μ := div_nonneg P.Lg_nonneg P.μ_pos.le
  have hr := P.response_distance_bound r x z
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))).2 hr
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  nlinarith [mul_nonneg hk (sq_nonneg ‖x - z‖)]

theorem upper_component_bounds (x z : X) (y w : Y) :
    ‖P.fx x y - P.fx z w‖ ≤ Lf * jointDistance x z y w ∧
      ‖P.fy x y - P.fy z w‖ ≤ Lf * jointDistance x z y w := by
  have h := P.smooth_f x z y w
  have hs : (jointDistance x z y w) ^ 2 = ‖x - z‖ ^ 2 + ‖y - w‖ ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hp : 0 ≤ Lf * jointDistance x z y w := mul_nonneg P.Lf_nonneg (Real.sqrt_nonneg _)
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    nlinarith [sq_nonneg ‖P.fy x y - P.fy z w‖]
  · apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    nlinarith [sq_nonneg ‖P.fx x y - P.fx z w‖]

/-- The exact universal curvature coefficient, with inverses at the two points
supplied by their equations. In finite dimension, `hessian_inverse_exists`
constructs those inverses from Primitive. -/
theorem hypergradient_with_inverse_bound (r : P.Response) (x z : X)
    (Jx Jz : Y →L[ℝ] Y)
    (hxl : ∀ v, Jx (P.gyy x (r.y x) v) = v)
    (hxr : ∀ v, P.gyy x (r.y x) (Jx v) = v)
    (hzr : ∀ v, P.gyy z (r.y z) (Jz v) = v) :
    ‖(P.fx x (r.y x) - P.gxy x (r.y x) (Jx (P.fy x (r.y x)))) -
      (P.fx z (r.y z) - P.gxy z (r.y z) (Jz (P.fy z (r.y z))))‖ ≤
      ((1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ)) * ‖x - z‖ := by
  have hu := P.upper_component_bounds x z (r.y x) (r.y z)
  have h := Curvature.hypergradient_difference (P.fx x (r.y x)) (P.fx z (r.y z))
    (P.fy x (r.y x)) (P.fy z (r.y z))
    (P.gxy x (r.y x)) (P.gxy z (r.y z))
    (P.gyy x (r.y x)) (P.gyy z (r.y z)) Jx Jz hxl hzr
    P.μ_pos P.Lg_nonneg P.ρ_nonneg (Real.sqrt_nonneg _)
    (P.hessian_inverse_norm x (r.y x) Jx hxr) (P.hessian_inverse_norm z (r.y z) Jz hzr)
    (P.mixed_hessian_norm x (r.y x)) (P.mixed_hessian_norm z (r.y z))
    (P.variation_xy x z (r.y x) (r.y z)) (P.variation_yy x z (r.y x) (r.y z))
    hu.1 hu.2 (P.upper_bound z (r.y z))
  have hc : 0 ≤ (1 + Lg / μ) * (Lf + ρ * Cf / μ) :=
    mul_nonneg (add_nonneg zero_le_one (div_nonneg P.Lg_nonneg P.μ_pos.le))
      (add_nonneg P.Lf_nonneg (div_nonneg (mul_nonneg P.ρ_nonneg P.Cf_nonneg) P.μ_pos.le))
  exact (h.trans (mul_le_mul_of_nonneg_left (P.response_joint_distance r x z) hc)).trans_eq (by ring)

include P in
theorem universal_curvature_nonneg : 0 ≤ (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) :=
  mul_nonneg (sq_nonneg _)
    (add_nonneg P.Lf_nonneg (div_nonneg (mul_nonneg P.ρ_nonneg P.Cf_nonneg) P.μ_pos.le))

variable [FiniteDimensional ℝ Y]

/-- The universal curvature bound for the actual composed hyperobjective. -/
theorem gradient_hyperobjective_norm_sub_le (r : P.Response) (x z : X) :
    ‖gradient (P.hyperobjective r) x - gradient (P.hyperobjective r) z‖ ≤
      ((1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ)) * ‖x - z‖ := by
  rw [P.gradient_hyperobjective r x, P.gradient_hyperobjective r z]
  exact P.hypergradient_with_inverse_bound r x z (P.inverseAt x (r.y x))
    (P.inverseAt z (r.y z)) (P.inverseAt_left x (r.y x))
    (P.inverseAt_right x (r.y x)) (P.inverseAt_right z (r.y z))

/-- Equation `up:eq:Lambda-universal`, with no unproved analytic certificates. -/
theorem gradient_hyperobjective_lipschitz (r : P.Response) :
    LipschitzWith ⟨(1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ), P.universal_curvature_nonneg⟩
      (gradient (P.hyperobjective r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simpa only [dist_eq_norm, NNReal.coe_mk] using P.gradient_hyperobjective_norm_sub_le r x z

end Bilevel.Model.Primitive
