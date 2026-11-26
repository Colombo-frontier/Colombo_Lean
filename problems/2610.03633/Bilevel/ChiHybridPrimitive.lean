import Bilevel.PartialLegendreHybridRegularity
import Bilevel.PartialLegendreHybridTrace
import Bilevel.GradientJetBounds

/-! The actual hybrid partial-conjugate Primitive with arbitrary upper
scalar and affine coupling. Both Hessian blocks come from the full joint
derivative; their variation is bounded by projection of that derivative. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiHybrid
open PrimitiveGeometry PartialLegendre ChiPrimitive
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem hybrid_primitive
    (P : Joint X Y → ℝ) {δ : NNReal} {G : Joint X Y → Joint X Y}
    (hG : LipschitzWith δ G) (hδ : δ<1) (hquarter : (δ:ℝ)≤1/4)
    (hP : ∀ z,HasGradientAt P (G z) z)
    (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hDG : ∀ z,HasFDerivAt G (B z) z) {H : ℝ} (hH : 0≤H)
    (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖)
    (m : ℝ) (hm : 0<m) (Q : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (hpsd : ∀ y,0≤⟪y,Q y⟫)
    (f : Joint X Y → ℝ) (hf : ContDiff ℝ 3 f)
    (μ Lf Lg Cf ρ : ℝ) (hμ : 0<μ) (hLf : 0≤Lf) (hLg : 0≤Lg) (hCf : 0≤Cf) (hρ : 0≤ρ)
    (hmodulus : μ≤m/(1+(δ:ℝ))) (hsmooth : 2*m+‖Q‖+‖C‖≤Lg) (hvariation : 3*m*H≤ρ)
    (hf2 : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤Lf)
    (hfy : ∀ x y,‖gradient (fun w => f (pack x w)) y‖≤Cf)
    (ystar : X → Y) (hstationary : ∀ x,m • jointSolution hG hδ x (ystar x)+Q (ystar x)=C x) :
    ∃ Pr : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ,
      (∀ x y,Pr.f x y=f (pack x y)) ∧
      (∀ x y,Pr.g x y=hybridLower hG hδ P m Q C (pack x y)) ∧
      (∀ x y,Pr.gy x y=m • jointSolution hG hδ x y+Q y-C x) ∧
      ∃ r : Pr.Response,(∀ x,r.y x=ystar x) ∧
        (∀ x,Pr.hyperobjective r x=f (pack x (ystar x))) ∧
        (∀ x y,Pr.IsLowerSolution x y ↔ y=ystar x) := by
  obtain ⟨K,hC,hD,_hN,hV,hgrad⟩ := hybridLower_regular hG hδ P hP hquarter B hDG hH hLip hm.le Q C hsym
  let lower := hybridLower hG hδ P m Q C
  have hstrong : ∀ x y w,lower (pack x y)+⟪gradient (fun v => lower (pack x v)) y,w-y⟫+
      μ/2*‖w-y‖^2≤lower (pack x w) := by
    intro x y w
    have hh := hybridLower_strong_model hG hδ P hP hm.le Q C hsym hpsd x y w
    have hm' : μ/2≤m/(2*(1+(δ:ℝ))) := by
      convert div_le_div_of_nonneg_right hmodulus (by norm_num : (0:ℝ)≤2) using 1
      rw [div_div]
      congr 1
      ring
    exact (add_le_add_left (mul_le_mul_of_nonneg_right hm' (sq_nonneg _)) _).trans hh
  have hfs := GradientJetBounds.gradient_lipschitz hf Lf hf2
  have hgs (z w : Joint X Y) : ‖gradient lower z-gradient lower w‖≤Lg*‖z-w‖ :=
    (hgrad z w).trans (mul_le_mul_of_nonneg_right hsmooth (norm_nonneg _))
  have hvs (z w : Joint X Y) : ‖K z-K w‖≤ρ*‖z-w‖ :=
    (hV z w).trans (mul_le_mul_of_nonneg_right hvariation (norm_nonneg _))
  let Pr := fromFull f lower (hf.differentiable (by norm_num)) (hC.differentiable (by norm_num))
    K hD μ Lf Lg Cf ρ hμ hLf hLg hCf hρ hstrong hfy hfs hgs hvs
  let r : Pr.Response := {
    y := ystar
    minimizes := fun x => (hybridLower_unique_response hG hδ P hP hm Q C hsym hpsd x (ystar x)
      (hstationary x) (ystar x)).mpr rfl }
  refine ⟨Pr,fun _ _ => rfl,fun _ _ => rfl,?_,r,fun _ => rfl,fun _ => rfl,?_⟩
  · intro x y
    change (gradient lower (pack x y)).snd=_
    rw [hybridLower_gradient hG hδ P hP m Q C hsym]
    change m • jointSolution hG hδ x y+(Q y-C x)=m • jointSolution hG hδ x y+Q y-C x
    abel
  · intro x y
    exact hybridLower_unique_response hG hδ P hP hm Q C hsym hpsd x (ystar x) (hstationary x) y

end Bilevel.ChiHybrid
