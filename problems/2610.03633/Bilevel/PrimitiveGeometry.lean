import Bilevel.Model
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Exact Euclidean full-gradient geometry behind the primitive interface.
The source product norm is the L2 product, not the maximum product norm. -/
noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

abbrev Joint (X Y : Type*) := WithLp 2 (X × Y)

def pack (x : X) (y : Y) : Joint X Y := (WithLp.equiv 2 (X × Y)).symm (x,y)

def packLinear : (X × Y) →L[ℝ] Joint X Y :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).symm.toContinuousLinearMap

omit [CompleteSpace X] [CompleteSpace Y] in
theorem norm_sq (z : Joint X Y) : ‖z‖ ^ 2 = ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, WithLp.prod_inner_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem norm_pack (x : X) (y : Y) : ‖pack x y‖ = Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  change ‖pack x y‖ = Real.sqrt (‖(pack x y).fst‖ ^ 2 + ‖(pack x y).snd‖ ^ 2)
  rw [← norm_sq (pack x y), Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem norm_sub_pack (x x' : X) (y y' : Y) :
    ‖pack x y-pack x' y'‖ = Model.jointDistance x x' y y' := by
  change ‖pack (x-x') (y-y')‖ = _
  exact norm_pack _ _

omit [CompleteSpace X] [CompleteSpace Y] in
theorem full_gradient_lipschitz_iff (fx : X → Y → X) (fy : X → Y → Y)
    {L : ℝ} (hL : 0 ≤ L) :
    (∀ x x' y y', ‖pack (fx x y) (fy x y)-pack (fx x' y') (fy x' y')‖ ≤
      L * ‖pack x y-pack x' y'‖) ↔
    (∀ x x' y y', ‖fx x y-fx x' y'‖ ^ 2+‖fy x y-fy x' y'‖ ^ 2 ≤
      L ^ 2 * (‖x-x'‖ ^ 2+‖y-y'‖ ^ 2)) := by
  constructor <;> intro h x x' y y'
  · have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr (h x x' y y')
    simpa only [mul_pow, norm_sq] using hh
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
    simpa only [mul_pow, norm_sq] using h x x' y y'

theorem partial_x {f : Joint X Y → ℝ} {gx : X} {gy : Y} {x : X} {y : Y}
    (hf : HasGradientAt f (pack gx gy) (pack x y)) :
    HasGradientAt (fun u => f (pack u y)) gx x := by
  have hp := (packLinear (X := X) (Y := Y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  have hh := hf.hasFDerivAt.comp x hp
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1
  ext v
  simp [packLinear, pack, ContinuousLinearMap.comp_apply, WithLp.prod_inner_apply]

theorem partial_y {f : Joint X Y → ℝ} {gx : X} {gy : Y} {x : X} {y : Y}
    (hf : HasGradientAt f (pack gx gy) (pack x y)) :
    HasGradientAt (fun v => f (pack x v)) gy y := by
  have hp := (packLinear (X := X) (Y := Y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))
  have hh := hf.hasFDerivAt.comp y hp
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1
  ext v
  simp [packLinear, pack, ContinuousLinearMap.comp_apply, WithLp.prod_inner_apply]

end Bilevel.PrimitiveGeometry
