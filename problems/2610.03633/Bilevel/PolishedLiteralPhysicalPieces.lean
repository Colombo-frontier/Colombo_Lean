import Bilevel.PolishedLiteralPieceSchedule
import Bilevel.PolishedLiteralCarry

/-! Exact scaling and radial/frame carry of the source's centered pieces. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainSchedule

theorem approximation_scaled (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ)
    (hβ : β≠0) (hδ : ∀ j,j<J → δ j≠0) (j : ℕ) :
    approximation n J L β δ j=ZeroChainResidualScaled.scaled
      (PolishedLiteralMultiscale.approximation n J (fun k => δ k/β) j) (L*β^2) β := by
  by_cases hj : j<J
  · funext z
    simp only [approximation,if_pos hj]
    rw [congrFun (flatResidual_scaled n L β (δ j) hβ (hδ j hj)) z]
    simp only [ZeroChainResidualScaled.scaled,PolishedLiteralMultiscale.approximation,if_pos hj]
  · funext z
    simp only [approximation,PolishedLiteralMultiscale.approximation,if_neg hj,
      ZeroChainResidualScaled.scaled,residual]

theorem piece_scaled (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ)
    (hβ : β≠0) (hδ : ∀ j,j<J → δ j≠0) (j : ℕ) :
    piece n J L β δ j=ZeroChainResidualScaled.scaled
      (PolishedLiteralMultiscale.piece n J (fun k => δ k/β) j) (L*β^2) β := by
  cases j with
  | zero => exact approximation_scaled n J L β δ hβ hδ 0
  | succ j =>
    funext z
    simp only [piece,PolishedLiteralMultiscale.piece,ZeroChainResidualScaled.scaled]
    rw [congrFun (approximation_scaled n J L β δ hβ hδ (j+1)) z,
      congrFun (approximation_scaled n J L β δ hβ hδ j) z]
    simp only [ZeroChainResidualScaled.scaled]
    ring

theorem resolution_div_beta (c β θ : ℝ) (hβ : β≠0) (j : ℕ) :
    resolution c β θ j/β=resolution c 1 θ j := by
  unfold resolution
  field_simp
  ring

namespace Parameters
open PrimitiveGeometry ChiRecursive RadialWrapper ZeroChainCarry
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

omit [CompleteSpace X] in
theorem microPiece_scaled (c θ : ℝ) (hc : 0<c) (hβ : 0<P.β) (hθ : 1≤θ)
    (hJ : P.J=levels θ) (hδ : P.δ=resolution c P.β θ)
    (i : Fin (P.macroNode.n+1)) (j : ℕ) :
    P.microPiece i j=fun u => (P.L*P.β^2)*
      PolishedLiteralMultiscale.piece P.n (levels θ) (resolution c 1 θ) j
        (P.β⁻¹ • P.coordinates i u) := by
  have hpos (k : ℕ) (_hk : k<P.J) : P.δ k≠0 := by
    rw [hδ]
    exact (resolution_pos c P.β θ hc hβ hθ k).ne'
  have hd : (fun k => P.δ k/P.β)=resolution c 1 θ := by
    funext k
    rw [hδ]
    exact resolution_div_beta c P.β θ hβ.ne' k
  funext u
  unfold microPiece
  rw [piece_scaled P.n P.J P.L P.β P.δ hβ.ne' hpos j,hJ,hd]
  rfl

end Parameters
end Bilevel.PolishedLiteral
