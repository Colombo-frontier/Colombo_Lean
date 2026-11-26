import Bilevel.PartialLegendreLowerRegularity

/-! Exact quadratic baseline for the prescribed primitive budgets. The
coupled blocks act on orthogonal coordinates, so their norms do not add
with the number of chain levels. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem normalConjugateProjection_adjoint (z : Joint X (Joint U V)) :
    (normalConjugateProjection : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V)).adjoint z=
      pack (pack z.fst (0:U)) z.snd := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left,normalConjugateProjection_apply]
  simp only [WithLp.prod_inner_apply]
  change ⟪z.fst,q.fst.fst⟫+(⟪z.snd.fst,q.snd.fst⟫+⟪z.snd.snd,q.snd.snd⟫)=
    (⟪z.fst,q.fst.fst⟫+⟪(0:U),q.fst.snd⟫)+(⟪z.snd.fst,q.snd.fst⟫+⟪z.snd.snd,q.snd.snd⟫)
  simp

theorem normalOuterProjection_adjoint (u : U) :
    (normalOuterProjection : FullNormalVariables X U V →L[ℝ] U).adjoint u=
      pack (pack (0:X) u) (0:Joint U V) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [WithLp.prod_inner_apply]
  change ⟪u,q.fst.snd⟫=(⟪(0:X),q.fst.fst⟫+⟪u,q.fst.snd⟫)+⟪(0:Joint U V),q.snd⟫
  simp

theorem normalTangentProjection_adjoint (u : U) :
    (normalTangentProjection : FullNormalVariables X U V →L[ℝ] U).adjoint u=
      pack (0:Joint X U) (pack u (0:V)) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [WithLp.prod_inner_apply]
  change ⟪u,q.snd.fst⟫=⟪(0:Joint X U),q.fst⟫+(⟪u,q.snd.fst⟫+⟪(0:V),q.snd.snd⟫)
  simp

def normalQuadraticOperator (m c : ℝ) : FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V :=
  let T : FullNormalVariables X U V →L[ℝ] Joint X (Joint U V) := normalConjugateProjection
  let A : FullNormalVariables X U V →L[ℝ] U := normalOuterProjection
  let B : FullNormalVariables X U V →L[ℝ] U := normalTangentProjection
  m • T.adjoint.comp (lowerProjection.comp T)-c • bilinearCouplingOperator A B

theorem normalQuadraticOperator_apply (m c : ℝ) (q : FullNormalVariables X U V) :
    normalQuadraticOperator m c q=
      pack (pack (0:X) ((-c) • q.snd.fst))
        (pack (m • q.snd.fst-c • q.fst.snd) (m • q.snd.snd)) := by
  simp only [normalQuadraticOperator,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,normalConjugateProjection_apply,lowerProjection_apply,
    normalConjugateProjection_adjoint,bilinearCouplingOperator,ContinuousLinearMap.add_apply,
    normalOuterProjection_adjoint,normalTangentProjection_adjoint]
  change pack (pack (m • (0:X)-c • (0+0)) (m • (0:U)-c • (q.snd.fst+0)))
    (pack (m • q.snd.fst-c • (0+q.fst.snd)) (m • q.snd.snd-c • ((0:V)+0)))= _
  simp

end Bilevel.PartialLegendre
