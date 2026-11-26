import Bilevel.PartialLegendreLowerRegularity

/-! Conversion of actual scalar objectives on Euclidean products to the
source Primitive interface. Every gradient and Hessian block is obtained
by differentiation and projection of the displayed objectives. -/
noncomputable section
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry PartialLegendre
open scoped RealInnerProductSpace
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

def rightInjection : Y →L[ℝ] Joint X Y :=
  packLinear.comp ((0 : Y →L[ℝ] X).prod (ContinuousLinearMap.id ℝ Y))

omit [CompleteSpace X] [CompleteSpace Y] in
theorem rightInjection_apply (y : Y) : rightInjection (X:=X) y=pack 0 y := rfl

omit [CompleteSpace X] [CompleteSpace Y] in
theorem rightInjection_norm : ‖(rightInjection : Y →L[ℝ] Joint X Y)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  rw [rightInjection_apply,norm_pack_zero_left,one_mul]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem jointFstLinear_norm : ‖(jointFstLinear : Joint X Y →L[ℝ] X)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  exact (WithLp.norm_fst_le X z).trans_eq (one_mul _).symm

omit [CompleteSpace X] [CompleteSpace Y] in
theorem jointSndLinear_norm : ‖(jointSndLinear : Joint X Y →L[ℝ] Y)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  exact (WithLp.norm_snd_le X z).trans_eq (one_mul _).symm

omit [CompleteSpace X] [CompleteSpace Y] in
theorem slice_hasFDerivAt (x : X) (y : Y) :
    HasFDerivAt (fun v : Y => pack x v) rightInjection y := by
  have hh := ((rightInjection (X:=X)).hasFDerivAt (x:=y)).add_const (pack x (0:Y))
  convert hh using 1
  funext v
  change pack x v=pack (0+x) (v+0)
  simp only [zero_add,add_zero]

theorem projected_hessian {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : Joint X Y → ℝ} {K : Joint X Y →L[ℝ] Joint X Y}
    (x : X) (y : Y) (hK : HasFDerivAt (gradient g) K (pack x y))
    (Q : Joint X Y →L[ℝ] Z) :
    HasFDerivAt (fun v => Q (gradient g (pack x v)))
      (Q.comp (K.comp rightInjection)) y :=
  Q.hasFDerivAt.comp y (hK.comp y (slice_hasFDerivAt x y))

omit [CompleteSpace X] [CompleteSpace Y] in
theorem projected_difference_bound {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Joint X Y →L[ℝ] Z) (hQ : ‖Q‖ ≤ 1)
    (K H : Joint X Y →L[ℝ] Joint X Y) :
    ‖Q.comp (K.comp rightInjection)-Q.comp (H.comp rightInjection)‖ ≤ ‖K-H‖ := by
  have he : Q.comp (K.comp rightInjection)-Q.comp (H.comp rightInjection)=
      Q.comp ((K-H).comp rightInjection) := by ext v; simp
  rw [he]
  calc
    _ ≤ ‖Q‖ * (‖K-H‖ * ‖(rightInjection : Y →L[ℝ] Joint X Y)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg Q))
    _ ≤ 1*(‖K-H‖*1) := by gcongr; exact rightInjection_norm
    _ = _ := by ring

def fromFull (f g : Joint X Y → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (K : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hK : ∀ z,HasFDerivAt (gradient g) (K z) z)
    (μ Lf Lg Cf ρ : ℝ) (hμ : 0 < μ) (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hCf : 0 ≤ Cf) (hρ : 0 ≤ ρ)
    (hstrong : ∀ x y w,g (pack x y)+⟪gradient (fun v => g (pack x v)) y,w-y⟫+
      μ/2*‖w-y‖^2 ≤ g (pack x w))
    (hupper : ∀ x y,‖gradient (fun v => f (pack x v)) y‖ ≤ Cf)
    (hfsmooth : ∀ z w,‖gradient f z-gradient f w‖ ≤ Lf*‖z-w‖)
    (hgsmooth : ∀ z w,‖gradient g z-gradient g w‖ ≤ Lg*‖z-w‖)
    (hvariation : ∀ z w,‖K z-K w‖ ≤ ρ*‖z-w‖) :
    Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ where
  μ_pos := hμ
  Lf_nonneg := hLf
  Lg_nonneg := hLg
  Cf_nonneg := hCf
  ρ_nonneg := hρ
  f x y := f (pack x y)
  g x y := g (pack x y)
  fx x y := (gradient f (pack x y)).fst
  fy x y := (gradient f (pack x y)).snd
  gx x y := (gradient g (pack x y)).fst
  gy x y := (gradient g (pack x y)).snd
  gyy x y := jointSndLinear.comp ((K (pack x y)).comp rightInjection)
  gxy x y := jointFstLinear.comp ((K (pack x y)).comp rightInjection)
  has_fx x y := partial_x (hf (pack x y)).hasGradientAt
  has_fy x y := partial_y (hf (pack x y)).hasGradientAt
  has_gx x y := partial_x (hg (pack x y)).hasGradientAt
  has_gy x y := partial_y (hg (pack x y)).hasGradientAt
  has_gyy x y := projected_hessian x y (hK (pack x y)) jointSndLinear
  has_gxy x y := projected_hessian x y (hK (pack x y)) jointFstLinear
  strong_convex x y w := by
    have hh := hstrong x y w
    rwa [(partial_y (hg (pack x y)).hasGradientAt).gradient] at hh
  upper_bound x y := by
    have hh := hupper x y
    rwa [(partial_y (hf (pack x y)).hasGradientAt).gradient] at hh
  smooth_f := (full_gradient_lipschitz_iff _ _ hLf).mp
    (fun x x' y y' => hfsmooth (pack x y) (pack x' y'))
  smooth_g := (full_gradient_lipschitz_iff _ _ hLg).mp
    (fun x x' y y' => hgsmooth (pack x y) (pack x' y'))
  variation_yy x x' y y' := by
    simpa only [norm_sub_pack] using
      (projected_difference_bound jointSndLinear jointSndLinear_norm (K (pack x y)) (K (pack x' y'))).trans
        (hvariation (pack x y) (pack x' y'))
  variation_xy x x' y y' := by
    simpa only [norm_sub_pack] using
      (projected_difference_bound jointFstLinear jointFstLinear_norm (K (pack x y)) (K (pack x' y'))).trans
        (hvariation (pack x y) (pack x' y'))

end Bilevel.ChiPrimitive
