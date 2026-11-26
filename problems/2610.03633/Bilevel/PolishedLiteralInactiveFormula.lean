import Bilevel.PolishedLiteralInactivePieces
import Bilevel.PolishedLiteralConservativeSignal

/-! The actual conservative inactive potential is exactly the source sum
of flattened inactive atoms, with the final atom corrected once. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral.Parameters
open PrimitiveGeometry PolishedLiteralCompensated
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

theorem inactivePerturbation_selected_formula (τ : ℝ)
    (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    P.inactivePerturbation τ (P.w P.J) y=
      P.μ/(2*P.L^2)*(P.selectedFlatResidual τ (uProj (Joint X U) y))^2-
      P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.selectedInactivePiece τ j (uProj (Joint X U) y)*
        PolishedLiteralCompensated.normal (P.w j) (sProj (Joint X U) y)) := by
  rw [P.inactivePerturbation_source]
  congr 2
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [P.selectedInactivePiece_eq τ j (by have := Finset.mem_range.mp hj;omega)]
    rw [if_neg (by have := Finset.mem_range.mp hj;omega),sub_zero]
  · rw [P.selectedInactivePiece_eq τ P.J le_rfl,if_pos rfl]

theorem inactiveSourceLower_selected_formula (τ : ℝ) (q : FullMeanSpace (X:=X) (U:=U)) :
    P.inactiveSourceLower τ (P.w P.J) q=
      lowerBase P.μ P.L q+P.μ/(2*P.L^2)*(P.selectedFlatResidual τ (pack q.fst.fst q.snd.fst))^2-
      P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.selectedInactivePiece τ j (pack q.fst.fst q.snd.fst)*
        PolishedLiteralCompensated.normal (P.w j) q.snd.snd) := by
  have hsplit : P.inactiveSourceLower τ (P.w P.J) q=
      lowerBase P.μ P.L q+P.inactivePerturbation τ (P.w P.J) (fullLowerEmbed q) := by
    unfold inactiveSourceLower signalFull inactivePerturbation
    rw [P.sourceLower_split]
    rw [P.sourcePerturbation_eq]
    simp only [Pi.sub_apply,Function.comp_apply]
    ring
  rw [hsplit,P.inactivePerturbation_selected_formula]
  have he : fullLowerEmbed q=PolishedLiteralCompensated.pack _ (PrimitiveGeometry.pack q.fst.fst q.snd.fst) q.snd.snd 0 := rfl
  rw [he,PolishedLiteralCompensated.uProj_pack,PolishedLiteralCompensated.sProj_pack]
  change lowerBase P.μ P.L q+(P.μ/(2*P.L^2)*(P.selectedFlatResidual τ (pack q.fst.fst q.snd.fst))^2-
    P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.selectedInactivePiece τ j (pack q.fst.fst q.snd.fst)*
      PolishedLiteralCompensated.normal (P.w j) q.snd.snd))=_
  ring

end Bilevel.PolishedLiteral.Parameters
