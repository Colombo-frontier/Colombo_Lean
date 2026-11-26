import Bilevel.ChiUpperNoisePrimitiveOracle

/-! The direct family's actual affine response yields the curvature clause
of the upper-noise theorem from Primitive smoothness itself. The Hessian-
variation budget does not enter this bound. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiUpperNoise
open PrimitiveGeometry PartialLegendre
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

theorem affine_response_curvature {μ L ρg κ : ℝ}
    (P : Model.Primitive (X:=Joint E U) (Y:=U) μ L L L ρg)
    (f : Queries E U → ℝ) (hf : Differentiable ℝ f)
    (hPf : ∀ x y,P.f x y=f (pack x y))
    (r : P.Response) (hr : ∀ x,r.y x=(κ/6) • x.snd) (hκ : 2≤κ)
    (x z : Joint E U) :
    ‖gradient (P.hyperobjective r) x-gradient (P.hyperobjective r) z‖≤(L*κ^2)*‖x-z‖ := by
  let A : Joint E U →L[ℝ] Queries E U :=
    packLinear.comp ((ContinuousLinearMap.id ℝ (Joint E U)).prod ((κ/6) • jointSndLinear))
  have hκ0 : 0≤κ := le_trans (by norm_num) hκ
  have hK : 0≤κ/6 := by positivity
  have hA : ‖A‖≤κ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hκ0
    intro w
    change ‖pack w ((κ/6) • w.snd)‖≤κ*‖w‖
    calc
      ‖pack w ((κ/6) • w.snd)‖≤‖w‖+‖(κ/6) • w.snd‖ := norm_pack_le_add _ _
      _ = ‖w‖+(κ/6)*‖w.snd‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hK]
      _ ≤ ‖w‖+(κ/6)*‖w‖ := add_le_add_left (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E w) hK) _
      _ ≤ κ*‖w‖ := by nlinarith only [hκ,norm_nonneg w]
  have hmean : P.hyperobjective r=f ∘ A := by
    funext w
    rw [Model.Primitive.hyperobjective,hPf,hr]
    rfl
  have hg (w : Joint E U) : gradient (P.hyperobjective r) w=A.adjoint (gradient f (A w)) := by
    rw [hmean]
    have hd := (hf (A w)).hasGradientAt.hasFDerivAt.comp w A.hasFDerivAt
    have hh : HasGradientAt (f ∘ A) (A.adjoint (gradient f (A w))) w := by
      apply hasGradientAt_iff_hasFDerivAt.mpr
      convert hd using 1
      ext v
      simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    exact hh.gradient
  have hgrad (q q' : Queries E U) : ‖gradient f q-gradient f q'‖≤L*‖q-q'‖ := by
    rw [upper_full_gradient P f hf hPf,upper_full_gradient P f hf hPf]
    exact (full_gradient_lipschitz_iff P.fx P.fy P.Lf_nonneg).mpr P.smooth_f q.fst q'.fst q.snd q'.snd
  rw [hg,hg,←map_sub]
  calc
    ‖A.adjoint (gradient f (A x)-gradient f (A z))‖≤‖A.adjoint‖*‖gradient f (A x)-gradient f (A z)‖ := A.adjoint.le_opNorm _
    _ = ‖A‖*‖gradient f (A x)-gradient f (A z)‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ κ*(L*‖A x-A z‖) := mul_le_mul hA (hgrad _ _) (norm_nonneg _) hκ0
    _ ≤ κ*(L*(κ*‖x-z‖)) := by
      apply mul_le_mul_of_nonneg_left _ hκ0
      apply mul_le_mul_of_nonneg_left _ P.Lf_nonneg
      rw [←map_sub]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    _ = (L*κ^2)*‖x-z‖ := by ring

theorem affine_response_lipschitz {μ L ρg κ : ℝ}
    (P : Model.Primitive (X:=Joint E U) (Y:=U) μ L L L ρg)
    (f : Queries E U → ℝ) (hf : Differentiable ℝ f)
    (hPf : ∀ x y,P.f x y=f (pack x y))
    (r : P.Response) (hr : ∀ x,r.y x=(κ/6) • x.snd) (hκ : 2≤κ) :
    LipschitzWith ⟨L*κ^2,mul_nonneg P.Lf_nonneg (sq_nonneg _)⟩ (gradient (P.hyperobjective r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simpa only [dist_eq_norm,NNReal.coe_mk] using affine_response_curvature P f hf hPf r hr hκ x z

end Bilevel.ChiUpperNoise
