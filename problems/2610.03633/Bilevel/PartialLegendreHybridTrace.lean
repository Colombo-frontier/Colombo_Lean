import Bilevel.PartialLegendreHybridBasic
import Bilevel.PartialLegendreNormalTrace

/-! The actual hybrid response follows from the zero normal trace and
the physical linear response equation. No response formula is assumed. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {δ : NNReal} {G : Joint X (Joint U V) → Joint X (Joint U V)}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X (Joint U V) → ℝ)
  (hP : ∀ z,HasGradientAt P (G z) z)
  (htrace : ∀ x p,P (pack x (pack p (0:V)))=0)

def hybridNormalResponse (tangent : X → U) (x : X) : Joint U V :=
  pack (tangent x) (G (pack x (pack (tangent x) (0:V)))).snd.snd

include hP htrace in
theorem hybrid_normal_solution (tangent : X → U) (x : X) :
    jointSolution hG hδ x (hybridNormalResponse (G:=G) tangent x)=pack (tangent x) (0:V) := by
  apply (jointSolution_of_equation hG hδ x _ _ _).symm
  exact trace_graph (fun z => P (pack x z)) (fun z => (G (pack x z)).snd)
    (jointSlice_hasGradientAt P hP x) (htrace x)
    (fun p => (G (pack x (pack p (0:V)))).snd.snd) (fun _ => rfl) (tangent x)

include hP htrace in
theorem hybrid_normal_stationary (m : ℝ) (Q : Joint U V →L[ℝ] Joint U V)
    (C : X →L[ℝ] Joint U V) (tangent : X → U)
    (hkill : ∀ v : V,Q (pack (0:U) v)=0)
    (hlinear : ∀ x,m • pack (tangent x) (0:V)+Q (pack (tangent x) (0:V))=C x) (x : X) :
    m • jointSolution hG hδ x (hybridNormalResponse (G:=G) tangent x)+
      Q (hybridNormalResponse (G:=G) tangent x)=C x := by
  rw [hybrid_normal_solution hG hδ P hP htrace]
  have he : hybridNormalResponse (G:=G) tangent x=
      pack (tangent x) (0:V)+pack (0:U) (G (pack x (pack (tangent x) (0:V)))).snd.snd := by
    change pack (tangent x) (G (pack x (pack (tangent x) (0:V)))).snd.snd=
      pack (tangent x+0) (0+(G (pack x (pack (tangent x) (0:V)))).snd.snd)
    simp only [add_zero,zero_add]
  rw [he,map_add,hkill,add_zero]
  exact hlinear x

include hP htrace in
theorem hybrid_normal_unique_response {m : ℝ} (hm : 0<m)
    (Q : Joint U V →L[ℝ] Joint U V) (C : X →L[ℝ] Joint U V)
    (hsym : ∀ u v,⟪Q u,v⟫=⟪u,Q v⟫) (hpsd : ∀ y,0≤⟪y,Q y⟫)
    (tangent : X → U) (hkill : ∀ v : V,Q (pack (0:U) v)=0)
    (hlinear : ∀ x,m • pack (tangent x) (0:V)+Q (pack (tangent x) (0:V))=C x)
    (x : X) (y : Joint U V) :
    (∀ w,hybridLower hG hδ P m Q C (pack x y)≤hybridLower hG hδ P m Q C (pack x w)) ↔
      y=hybridNormalResponse (G:=G) tangent x :=
  hybridLower_unique_response hG hδ P hP hm Q C hsym hpsd x _
    (hybrid_normal_stationary hG hδ P hP htrace m Q C tangent hkill hlinear x) y

end Bilevel.PartialLegendre
