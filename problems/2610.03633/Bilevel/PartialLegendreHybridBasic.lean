import Bilevel.ChiQuadraticLower
import Bilevel.ChiExtensionStrongConvex

/-! Actual partial-conjugate lower scalar with a positive-semidefinite
quadratic correction and a general bounded linear coupling. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G : Joint X Y → Joint X Y}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X Y → ℝ)

def hybridLower (m : ℝ) (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y) (z : Joint X Y) : ℝ :=
  m*jointConjugate hG hδ P z+ChiQuadratic.lower Q C z

variable (hP : ∀ z,HasGradientAt P (G z) z)
include hP

theorem hybridLower_hasGradientAt (m : ℝ) (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (z : Joint X Y) :
    HasGradientAt (hybridLower hG hδ P m Q C)
      (m • jointGradient hG hδ z+ChiQuadratic.hessian Q C z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert ((jointConjugate_hasGradientAt hG hδ P hP z).hasFDerivAt.const_mul m).add
    (ChiQuadratic.lower_hasGradientAt Q C hsym z).hasFDerivAt using 1
  ext w
  simp [InnerProductSpace.toDual_apply,inner_add_left,real_inner_smul_left]

theorem hybridLower_gradient (m : ℝ) (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (z : Joint X Y) :
    gradient (hybridLower hG hδ P m Q C) z=
      m • jointGradient hG hδ z+ChiQuadratic.hessian Q C z :=
  (hybridLower_hasGradientAt hG hδ P hP m Q C hsym z).gradient

theorem hybridLower_partial_gradient (m : ℝ) (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (x : X) (y : Y) :
    gradient (fun w => hybridLower hG hδ P m Q C (pack x w)) y=
      m • jointSolution hG hδ x y+Q y-C x := by
  have hh := PrimitiveGeometry.partial_y (hybridLower_hasGradientAt hG hδ P hP m Q C hsym (pack x y))
  convert hh.gradient using 1
  change m • jointSolution hG hδ x y+Q y-C x=
    m • jointSolution hG hδ x y+(Q y-C x)
  abel

theorem hybridLower_strong_model {m : ℝ} (hm : 0≤m)
    (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (hpsd : ∀ y,0≤⟪y,Q y⟫)
    (x : X) (y w : Y) :
    hybridLower hG hδ P m Q C (pack x y)+
      ⟪gradient (fun v => hybridLower hG hδ P m Q C (pack x v)) y,w-y⟫+
      m/(2*(1+(δ:ℝ)))*‖w-y‖^2≤hybridLower hG hδ P m Q C (pack x w) := by
  rw [hybridLower_partial_gradient hG hδ P hP m Q C hsym]
  have hc := mul_le_mul_of_nonneg_left
    (conjugate_strong_model hδ (jointSlice_lipschitz hG x) (fun z => P (pack x z))
      (jointSlice_hasGradientAt P hP x) y w) hm
  have hq := ChiQuadratic.lower_remainder Q C hsym x y w
  have hp := hpsd (w-y)
  change m*(jointConjugate hG hδ P (pack x y)+⟪jointSolution hG hδ x y,w-y⟫+
      1/(2*(1+(δ:ℝ)))*‖w-y‖^2)≤m*jointConjugate hG hδ P (pack x w) at hc
  have hc' : m*jointConjugate hG hδ P (pack x y)+m*⟪jointSolution hG hδ x y,w-y⟫+
      m/(2*(1+(δ:ℝ)))*‖w-y‖^2≤m*jointConjugate hG hδ P (pack x w) := by
    convert hc using 1
    ring
  unfold hybridLower
  simp only [inner_sub_left,inner_add_left,real_inner_smul_left] at hq hp ⊢
  linarith only [hc',hq,hp]

theorem hybridLower_unique_response {m : ℝ} (hm : 0<m)
    (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (hpsd : ∀ y,0≤⟪y,Q y⟫)
    (x : X) (ystar : Y)
    (hstationary : m • jointSolution hG hδ x ystar+Q ystar=C x) (y : Y) :
    (∀ w,hybridLower hG hδ P m Q C (pack x y)≤hybridLower hG hδ P m Q C (pack x w)) ↔ y=ystar := by
  have hg : gradient (fun w => hybridLower hG hδ P m Q C (pack x w)) ystar=0 := by
    rw [hybridLower_partial_gradient hG hδ P hP m Q C hsym,hstationary,sub_self]
  have hgrowth := hybridLower_strong_model hG hδ P hP hm.le Q C hsym hpsd x ystar
  have hp : 0<m/(2*(1+(δ:ℝ))) := by positivity
  constructor
  · intro hy
    have hh := hgrowth y
    rw [hg,inner_zero_left,add_zero] at hh
    have hb := hy ystar
    have he : ‖y-ystar‖^2=0 := by nlinarith only [hh,hb,hp,sq_nonneg ‖y-ystar‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))
  · rintro rfl w
    have hh := hgrowth w
    rw [hg,inner_zero_left,add_zero] at hh
    exact le_trans (le_add_of_nonneg_right (mul_nonneg hp.le (sq_nonneg _))) hh

end Bilevel.PartialLegendre
