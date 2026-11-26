import Smoothness2601.Population
import Smoothness2601.SineLift

/-! Actual full Euclidean gradients and lower-variable Hessian blocks of the
sine hard instance, before choosing its numerical scales. -/
noncomputable section
open scoped RealInnerProductSpace
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.SineGeometry
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

def first : Joint X ℝ →L[ℝ] X := (ContinuousLinearMap.fst ℝ X ℝ).comp
  (WithLp.prodContinuousLinearEquiv 2 ℝ X ℝ).toContinuousLinearMap
def second : Joint X ℝ →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ X ℝ).comp
  (WithLp.prodContinuousLinearEquiv 2 ℝ X ℝ).toContinuousLinearMap

def upper (A : X → ℝ) (b : ℝ) (z : Joint X ℝ) : ℝ := A z.fst+b*z.snd
def lower (B : X → ℝ) (m a h : ℝ) (z : Joint X ℝ) : ℝ :=
  SineLift.lowerObjective m a h (B z.fst) z.snd

def upperGradient (gA : X → X) (b : ℝ) (z : Joint X ℝ) : Joint X ℝ := pack (gA z.fst) b
def lowerGradient (B : X → ℝ) (gB : X → X) (m a h : ℝ) (z : Joint X ℝ) : Joint X ℝ :=
  pack ((-m*a*h*Real.sin (z.snd/h)) • gB z.fst)
    (SineLift.lowerGradient m a h (B z.fst) z.snd)

theorem upper_hasGradientAt (A : X → ℝ) (gA : X → X)
    (hA : ∀ x, HasGradientAt A (gA x) x) (b : ℝ) (z : Joint X ℝ) :
    HasGradientAt (upper A b) (upperGradient gA b z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := ((hA z.fst).hasFDerivAt.comp z (first (X := X)).hasFDerivAt).add
    ((second (X := X)).hasFDerivAt.const_mul b)
  convert hd using 1
  ext v
  simp only [upperGradient,InnerProductSpace.toDual_apply,WithLp.prod_inner_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp [first,second,pack,RCLike.inner_apply,mul_comm]

theorem lower_hasGradientAt (B : X → ℝ) (gB : X → X)
    (hB : ∀ x, HasGradientAt B (gB x) x) (m a : ℝ) {h : ℝ} (hh : h ≠ 0)
    (z : Joint X ℝ) : HasGradientAt (lower B m a h) (lowerGradient B gB m a h z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hx := (hB z.fst).hasFDerivAt.comp z (first (X := X)).hasFDerivAt
  have hy := (second (X := X)).hasFDerivAt (x := z)
  have hdv : HasFDerivAt (fun z : Joint X ℝ => z.snd/h) (h⁻¹ • second) z := by
    convert hy.const_mul h⁻¹ using 1
    funext v
    change v.snd/h = h⁻¹*v.snd
    ring
  have hs := (Real.hasDerivAt_sin (z.snd/h)).comp_hasFDerivAt z hdv
  have hd := (hy.mul hy).const_mul (m/2) |>.sub
    ((hx.mul hs).const_mul (m*a*h))
  convert hd using 1
  · funext v
    change m/2*v.snd^2-m*a*h*B v.fst*Real.sin (v.snd/h) =
      m/2*(v.snd*v.snd)-m*a*h*(B v.fst*Real.sin (v.snd/h))
    ring
  · ext v
    simp only [lowerGradient,InnerProductSpace.toDual_apply,WithLp.prod_inner_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    simp [first,second,pack,SineLift.lowerGradient,RCLike.inner_apply,real_inner_smul_left]
    field_simp
    ring

def mixedBlock (gB : X → X) (m a h : ℝ) (x : X) (y : ℝ) : ℝ →L[ℝ] X :=
  (1 : ℝ →L[ℝ] ℝ).smulRight ((-m*a*Real.cos (y/h)) • gB x)

def lowerBlock (B : X → ℝ) (m a h : ℝ) (x : X) (y : ℝ) : ℝ →L[ℝ] ℝ :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (m*(1+(a/h)*B x*Real.sin (y/h)))

omit [CompleteSpace X] in
theorem has_mixedBlock (B : X → ℝ) (gB : X → X) (m a : ℝ) {h : ℝ} (hh : h ≠ 0)
    (x : X) (y : ℝ) :
    HasFDerivAt (fun v => (lowerGradient B gB m a h (pack x v)).fst) (mixedBlock gB m a h x y) y := by
  have hd := (((hasDerivAt_id y).div_const h).sin.const_mul (-m*a*h)).smul_const (gB x)
  have hd' : HasDerivAt (fun v => (lowerGradient B gB m a h (pack x v)).fst)
      ((-m*a*Real.cos (y/h)) • gB x) y := by
    convert hd using 1
    congr 1
    dsimp
    field_simp
    ring
  exact hd'.hasFDerivAt

omit [CompleteSpace X] in
theorem has_lowerBlock (B : X → ℝ) (gB : X → X) (m a h : ℝ) (x : X) (y : ℝ) :
    HasFDerivAt (fun v => (lowerGradient B gB m a h (pack x v)).snd) (lowerBlock B m a h x y) y :=
  (SineLift.hasDerivAt_lowerGradient m a h (B x) y).hasFDerivAt

end Smoothness2601.SineGeometry
