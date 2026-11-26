import Bilevel.ChiUpperNoisePrimitiveOracle

/-! Actual hyperobjective curvature for a linear response graph. This
uses the same Primitive's upper smoothness, with no Hessian-variation term. -/
noncomputable section
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem affine_graph_gradient_lipschitz {μ Lf Lg Cf ρ b : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f : Joint X Y → ℝ) (hf : Differentiable ℝ f)
    (hPf : ∀ x y,P.f x y=f (pack x y)) (r : P.Response)
    (A : X →L[ℝ] Joint X Y) (hr : ∀ x,A x=pack x (r.y x))
    (hb : 0≤b) (hA : ‖A‖≤b) :
    LipschitzWith ⟨Lf*b^2,mul_nonneg P.Lf_nonneg (sq_nonneg _)⟩ (gradient (P.hyperobjective r)) := by
  have hmean : P.hyperobjective r=f ∘ A := by
    funext x
    rw [Model.Primitive.hyperobjective,hPf,Function.comp_apply,hr]
  have hg (x : X) : gradient (P.hyperobjective r) x=A.adjoint (gradient f (A x)) := by
    rw [hmean]
    have hd := (hf (A x)).hasGradientAt.hasFDerivAt.comp x A.hasFDerivAt
    have hh : HasGradientAt (f ∘ A) (A.adjoint (gradient f (A x))) x := by
      apply hasGradientAt_iff_hasFDerivAt.mpr
      convert hd using 1
      ext v
      simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    exact hh.gradient
  have hgrad (q q' : Joint X Y) : ‖gradient f q-gradient f q'‖≤Lf*‖q-q'‖ := by
    rw [ChiUpperNoise.upper_full_gradient P f hf hPf,ChiUpperNoise.upper_full_gradient P f hf hPf]
    exact (full_gradient_lipschitz_iff P.fx P.fy P.Lf_nonneg).mpr P.smooth_f q.fst q'.fst q.snd q'.snd
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [dist_eq_norm,NNReal.coe_mk]
  rw [hg,hg,←map_sub]
  calc
    ‖A.adjoint (gradient f (A x)-gradient f (A z))‖≤‖A.adjoint‖*‖gradient f (A x)-gradient f (A z)‖ := A.adjoint.le_opNorm _
    _ = ‖A‖*‖gradient f (A x)-gradient f (A z)‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ b*(Lf*‖A x-A z‖) := mul_le_mul hA (hgrad _ _) (norm_nonneg _) hb
    _ ≤ b*(Lf*(b*‖x-z‖)) := by
      apply mul_le_mul_of_nonneg_left _ hb
      apply mul_le_mul_of_nonneg_left _ P.Lf_nonneg
      rw [←map_sub]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    _ = (Lf*b^2)*‖x-z‖ := by ring

end Bilevel.ChiPrimitive
