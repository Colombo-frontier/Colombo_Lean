import Bilevel.ChiHybridPrimitive

/-! The hybrid Primitive directly from actual extension jets and a zero-normal
trace. The response is derived from the physical linear equation; no inverse
or envelope-gradient formula is part of the assumptions. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiHybrid
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem extensionGradientLipschitz (P : Joint X (Joint U V) → ℝ) (hP : ContDiff ℝ 3 P)
    (δ : NNReal) (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) :
    LipschitzWith δ (gradient P) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm] using GradientJetBounds.gradient_lipschitz hP δ h2 z w

def lowerOfExtension (P : Joint X (Joint U V) → ℝ) (hP : ContDiff ℝ 3 P)
    (δ : NNReal) (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) (hδ : δ<1)
    (m : ℝ) (Q : Joint U V →L[ℝ] Joint U V) (C : X →L[ℝ] Joint U V) :
    Joint X (Joint U V) → ℝ :=
  hybridLower (extensionGradientLipschitz P hP δ h2) hδ P m Q C

def responseOfExtension (P : Joint X (Joint U V) → ℝ) (tangent : X → U) (x : X) : Joint U V :=
  pack (tangent x) (gradient P (pack x (pack (tangent x) (0:V)))).snd.snd

theorem hybrid_primitive_of_extension_jets
    (P : Joint X (Joint U V) → ℝ) (hP : ContDiff ℝ 3 P)
    (δ : NNReal) (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) (hδ : δ<1)
    (hsmall : (δ:ℝ)≤1/4) (hzero : ∀ x p,P (pack x (pack p (0:V)))=0)
    (m : ℝ) (hm : 0<m) (Q : Joint U V →L[ℝ] Joint U V) (C : X →L[ℝ] Joint U V)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (hpsd : ∀ y,0≤⟪y,Q y⟫)
    (tangent : X → U) (hkill : ∀ v : V,Q (pack (0:U) v)=0)
    (hlinear : ∀ x,m • pack (tangent x) (0:V)+Q (pack (tangent x) (0:V))=C x)
    (f : Joint X (Joint U V) → ℝ) (hf : ContDiff ℝ 3 f)
    (μ Lf Lg Cf ρ : ℝ) (hμ : 0<μ) (hLf : 0≤Lf) (hLg : 0≤Lg) (hCf : 0≤Cf) (hρ : 0≤ρ)
    (hmodulus : μ≤m/(1+(δ:ℝ))) (hsmooth : 2*m+‖Q‖+‖C‖≤Lg)
    (h3 : ∀ z,‖iteratedFDeriv ℝ 3 P z‖≤ρ/(3*m))
    (hf2 : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤Lf)
    (hfy : ∀ x y,‖gradient (fun w => f (pack x w)) y‖≤Cf) :
    ∃ Pr : Model.Primitive (X:=X) (Y:=Joint U V) μ Lf Lg Cf ρ,
      (∀ x y,Pr.f x y=f (pack x y)) ∧
      (∀ x y,Pr.g x y=lowerOfExtension P hP δ h2 hδ m Q C (pack x y)) ∧
      ∃ r : Pr.Response,(∀ x,r.y x=responseOfExtension P tangent x) ∧
        (∀ x,Pr.hyperobjective r x=f (pack x (responseOfExtension P tangent x))) ∧
        (∀ x y,Pr.IsLowerSolution x y ↔ y=responseOfExtension P tangent x) := by
  have hG := extensionGradientLipschitz P hP δ h2
  have hgrad : ∀ z,HasGradientAt P (gradient P z) z :=
    fun z => ((hP.differentiable (by norm_num)) z).hasGradientAt
  let B := fderiv ℝ (gradient P)
  have hDG : ∀ z,HasFDerivAt (gradient P) (B z) z := fun z =>
    (((GradientJetBounds.gradient_contDiff hP).differentiable (by norm_num)) z).hasFDerivAt
  have hH : 0≤ρ/(3*m) := by positivity
  have hLip := GradientJetBounds.hessian_lipschitz hP (ρ/(3*m)) h3
  have hstationary (x : X) :
      m • jointSolution hG hδ x (responseOfExtension P tangent x)+
        Q (responseOfExtension P tangent x)=C x :=
    hybrid_normal_stationary hG hδ P hgrad hzero m Q C tangent hkill hlinear x
  have hvar : 3*m*(ρ/(3*m))≤ρ := by
    have he : 3*m*(ρ/(3*m))=ρ := by field_simp
    exact he.le
  obtain ⟨Pr,hfPr,hgPr,_,r,hr,hmean,hunique⟩ := hybrid_primitive P hG hδ hsmall hgrad B hDG
    hH hLip m hm Q C hsym hpsd f hf μ Lf Lg Cf ρ hμ hLf hLg hCf hρ
    hmodulus hsmooth hvar hf2 hfy (responseOfExtension P tangent) hstationary
  exact ⟨Pr,hfPr,hgPr,r,hr,hmean,hunique⟩

end Bilevel.ChiHybrid
