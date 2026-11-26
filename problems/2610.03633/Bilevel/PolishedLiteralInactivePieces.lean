import Bilevel.PolishedLiteralResidualLocality
import Bilevel.PolishedLiteralFlatEnvelope

/-! The actual source inactive final atom is a telescope of flattened
residuals only. This makes its disclosed-prefix locality explicit for the
same functions used by the conservative oracle. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry

def inactiveApproximation (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ) (j : ℕ) : Space n → ℝ :=
  if j<J then flatResidual n L β (δ j) else flatResidual n L β τ

def inactivePiece (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ) : ℕ → Space n → ℝ
  | 0 => inactiveApproximation n J L β δ τ 0
  | j+1 => fun z => inactiveApproximation n J L β δ τ (j+1) z-inactiveApproximation n J L β δ τ j z

theorem inactivePiece_eq_source (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ)
    (j : ℕ) (hj : j≤J) (z : Space n) :
    inactivePiece n J L β δ τ j z=piece n J L β δ j z-
      (if j=J then residual n L β z-flatResidual n L β τ z else 0) := by
  cases j with
  | zero =>
    by_cases hJ : J=0
    · subst J
      simp only [inactivePiece,inactiveApproximation,piece,approximation,lt_self_iff_false,if_false,if_true]
      ring
    · have h0 : 0<J := by omega
      simp only [inactivePiece,inactiveApproximation,piece,approximation,if_pos h0,
        if_neg (Ne.symm hJ),sub_zero]
  | succ j =>
    have hp : j<J := by omega
    by_cases he : j+1=J
    · have hn : ¬j+1<J := by omega
      simp only [inactivePiece,inactiveApproximation,piece,approximation,if_neg hn,if_pos hp,if_pos he]
      ring
    · have hn : j+1<J := by omega
      simp only [inactivePiece,inactiveApproximation,piece,approximation,if_pos hn,if_pos hp,if_neg he,sub_zero]

theorem inactiveApproximation_contDiff (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ) (j : ℕ) :
    ContDiff ℝ 3 (inactiveApproximation n J L β δ τ j) := by
  unfold inactiveApproximation
  split_ifs
  · exact flatResidual_contDiff n L β (δ j)
  · exact flatResidual_contDiff n L β τ

theorem inactivePiece_contDiff (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ) (j : ℕ) :
    ContDiff ℝ 3 (inactivePiece n J L β δ τ j) := by
  cases j with
  | zero => exact inactiveApproximation_contDiff n J L β δ τ 0
  | succ j =>
    exact (inactiveApproximation_contDiff n J L β δ τ (j+1)).sub
      (inactiveApproximation_contDiff n J L β δ τ j)

theorem inactiveApproximation_prefix_value (n J r : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ)
    (hτ : 0<τ) (hδ : ∀ j,j<J → τ≤δ j) (j : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤τ) :
    inactiveApproximation n J L β δ τ j z=inactiveApproximation n J L β δ τ j (retain n r z) := by
  unfold inactiveApproximation
  split_ifs with hj
  · exact flatResidual_prefix_value n r L β (δ j) (hτ.trans_le (hδ j hj)) z
      (fun k hk => (hz k hk).trans (hδ j hj))
  · exact flatResidual_prefix_value n r L β τ hτ z hz

theorem inactivePiece_prefix_value (n J r : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ)
    (hτ : 0<τ) (hδ : ∀ j,j<J → τ≤δ j) (j : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤τ) :
    inactivePiece n J L β δ τ j z=inactivePiece n J L β δ τ j (retain n r z) := by
  cases j with
  | zero => exact inactiveApproximation_prefix_value n J r L β δ τ hτ hδ 0 z hz
  | succ j =>
    simp only [inactivePiece]
    rw [inactiveApproximation_prefix_value n J r L β δ τ hτ hδ (j+1) z hz,
      inactiveApproximation_prefix_value n J r L β δ τ hτ hδ j z hz]

theorem inactivePiece_wrapped_prefix {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n J r : ℕ) (L β R : ℝ) (δ : ℕ → ℝ) (τ : ℝ) (hR : 0<R)
    (hτ : 0<τ) (hδ : ∀ j,j<J → τ≤δ j) (j : ℕ)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<τ) :
    inactivePiece n J L β δ τ j (WrappedChain.coordinates n R U u)=
      prefixWrapped n r R U (inactivePiece n J L β δ τ j) u ∧
    gradient (inactivePiece n J L β δ τ j ∘ WrappedChain.coordinates n R U) u=
      gradient (prefixWrapped n r R U (inactivePiece n J L β δ τ j)) u :=
  wrapped_prefix_of_value _ ((inactivePiece_contDiff n J L β δ τ j).differentiable (by norm_num))
    (inactivePiece_prefix_value n J r L β δ τ hτ hδ j) R hR U u hu

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def selectedInactivePiece (τ : ℝ) (j : ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),wrappedSelector P.macroNode i z.fst*
    inactivePiece P.n P.J P.L P.β P.δ τ j (P.coordinates i z.snd)

theorem selectedInactivePiece_eq (τ : ℝ) (j : ℕ) (hj : j≤P.J) (z : Joint X U) :
    P.selectedInactivePiece τ j z=P.selectedPiece j z-
      (if j=P.J then P.residualDifference τ z else 0) := by
  simp only [selectedInactivePiece,inactivePiece_eq_source P.n P.J P.L P.β P.δ τ j hj]
  by_cases he : j=P.J
  · simp only [if_pos he,mul_sub,Finset.sum_sub_distrib]
    rfl
  · simp only [if_neg he,sub_zero]
    rfl

end Parameters
end Bilevel.PolishedLiteral
