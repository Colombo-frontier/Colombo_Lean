import Bilevel.ChiPrimitiveAssembly

/-! Full joint calculus for an actual exact-quadratic lower objective with
an arbitrary bounded coupling. The cross-block operator norm is charged
once, using the Euclidean product norm. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiQuadratic
open PrimitiveGeometry PartialLegendre
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

def lower (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y) (z : Joint X Y) : ℝ :=
  (1/2)*⟪z.snd,H z.snd⟫-⟪C z.fst,z.snd⟫

def hessian (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y) : Joint X Y →L[ℝ] Joint X Y :=
  packLinear.comp ((-C.adjoint.comp jointSndLinear).prod
    (H.comp jointSndLinear-C.comp jointFstLinear))

theorem hessian_apply (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y) (z : Joint X Y) :
    hessian H C z=pack (-C.adjoint z.snd) (H z.snd-C z.fst) := rfl

omit [CompleteSpace X] [CompleteSpace Y] in
theorem lower_contDiff (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y) (k : ℕ) :
    ContDiff ℝ k (lower H C) := by
  let A : Joint X Y →L[ℝ] X := jointFstLinear
  let B : Joint X Y →L[ℝ] Y := jointSndLinear
  exact (contDiff_const.mul (B.contDiff.inner ℝ (H.contDiff.comp B.contDiff))).sub
    ((C.contDiff.comp A.contDiff).inner ℝ B.contDiff)

theorem lower_hasGradientAt (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) (z : Joint X Y) :
    HasGradientAt (lower H C) (hessian H C z) z := by
  let A : Joint X Y →L[ℝ] X := jointFstLinear
  let B : Joint X Y →L[ℝ] Y := jointSndLinear
  have hq := B.hasFDerivAt.inner ℝ (H.hasFDerivAt.comp z B.hasFDerivAt) (x:=z)
  have hc := (C.hasFDerivAt.comp z A.hasFDerivAt).inner ℝ B.hasFDerivAt (x:=z)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (hq.const_mul (1/2)).sub hc using 1
  ext w
  simp only [InnerProductSpace.toDual_apply,hessian_apply,WithLp.prod_inner_apply]
  change ⟪-C.adjoint z.snd,w.fst⟫+⟪H z.snd-C z.fst,w.snd⟫= _
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,inner_sub_left,inner_neg_left,ContinuousLinearMap.adjoint_inner_left,smul_eq_mul]
  change -⟪z.snd,C w.fst⟫+(⟪H z.snd,w.snd⟫-⟪C z.fst,w.snd⟫)=
    (1/2)*(⟪z.snd,H w.snd⟫+⟪w.snd,H z.snd⟫)-(⟪C z.fst,w.snd⟫+⟪C w.fst,z.snd⟫)
  linarith only [hsym z.snd w.snd,real_inner_comm w.snd (H z.snd),real_inner_comm (C w.fst) z.snd]

theorem lower_gradient (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) : gradient (lower H C)=hessian H C :=
  funext (fun z => (lower_hasGradientAt H C hsym z).gradient)

theorem hessian_norm_bound (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y) :
    ‖hessian H C‖≤‖H‖+‖C‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hcross : ‖pack (-C.adjoint z.snd) (-C z.fst)‖≤‖C‖*‖z‖ := by
    have ha := C.adjoint.le_opNorm z.snd
    rw [ContinuousLinearMap.adjoint.norm_map] at ha
    have hb := C.le_opNorm z.fst
    have has := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ha
    have hbs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,norm_sq z,norm_sq]
    change ‖-C.adjoint z.snd‖^2+‖-C z.fst‖^2≤‖C‖^2*(‖z.fst‖^2+‖z.snd‖^2)
    rw [norm_neg,norm_neg]
    nlinarith only [has,hbs]
  have hdiag : ‖pack (0:X) (H z.snd)‖≤‖H‖*‖z‖ := by
    rw [norm_pack_zero_left]
    exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le X z) (norm_nonneg H))
  have he : hessian H C z=pack (0:X) (H z.snd)+pack (-C.adjoint z.snd) (-C z.fst) := by
    rw [hessian_apply]
    change pack (-C.adjoint z.snd) (H z.snd-C z.fst)=pack (0+ -C.adjoint z.snd) (H z.snd+ -C z.fst)
    simp only [zero_add,sub_eq_add_neg]
  rw [he]
  exact (norm_add_le _ _).trans (by nlinarith only [hcross,hdiag])

omit [CompleteSpace X] [CompleteSpace Y] in
theorem lower_remainder (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) (x : X) (y w : Y) :
    lower H C (pack x w)-lower H C (pack x y)-⟪H y-C x,w-y⟫=
      ⟪w-y,H (w-y)⟫/2 := by
  change (1/2)*⟪w,H w⟫-⟪C x,w⟫-((1/2)*⟪y,H y⟫-⟪C x,y⟫)-⟪H y-C x,w-y⟫=
    ⟪w-y,H (w-y)⟫/2
  simp only [map_sub,inner_sub_left,inner_sub_right]
  have hcross : ⟪w,H y⟫=⟪y,H w⟫ := (real_inner_comm _ _).trans (hsym y w)
  rw [hsym y w,hsym y y,hcross]
  ring

theorem lower_strong_convex (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) {μ : ℝ}
    (hcoerce : ∀ y,μ*‖y‖^2≤⟪y,H y⟫) (x : X) (y w : Y) :
    lower H C (pack x y)+⟪gradient (fun v => lower H C (pack x v)) y,w-y⟫+
      μ/2*‖w-y‖^2≤lower H C (pack x w) := by
  have hg := PrimitiveGeometry.partial_y (lower_hasGradientAt H C hsym (pack x y))
  change HasGradientAt (fun v => lower H C (pack x v)) (H y-C x) y at hg
  rw [hg.gradient]
  have he := lower_remainder H C hsym x y w
  have hc := hcoerce (w-y)
  linarith only [he,hc]

end Bilevel.ChiQuadratic
