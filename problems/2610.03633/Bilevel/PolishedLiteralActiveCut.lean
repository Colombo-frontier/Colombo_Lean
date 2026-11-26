import Bilevel.PolishedLiteralInactiveCut

/-! Deterministic active mean reply cut: a Bernoulli activation adds only
the next column of the currently eligible micro block. Future macro
selector jets vanish at this fixed query. -/
noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators Topology
open Filter
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiPrefixEvaluation PrimitiveGeometry

theorem approximation_prefix_value_next (n J k : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ)
    (hβ : 0<β) (hτ : 0<τ) (hτβ : τ≤β/4) (hδ : ∀ j,j<J → τ≤δ j)
    (j : ℕ) (z : Space n)
    (hz : ∀ l : Fin (n+1),k≤l.val → |z l|≤τ) :
    approximation n J L β δ j z=approximation n J L β δ j (retain n (k+1) z) := by
  unfold approximation
  split_ifs with hj
  · exact flatResidual_prefix_value n (k+1) L β (δ j) (hτ.trans_le (hδ j hj)) z
      (fun l hl => (hz l (by omega)).trans (hδ j hj))
  · exact residual_prefix_value n k L β hβ z (fun l hl => (hz l hl).trans hτβ)

theorem piece_prefix_value_next (n J k : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (τ : ℝ)
    (hβ : 0<β) (hτ : 0<τ) (hτβ : τ≤β/4) (hδ : ∀ j,j<J → τ≤δ j)
    (j : ℕ) (z : Space n)
    (hz : ∀ l : Fin (n+1),k≤l.val → |z l|≤τ) :
    piece n J L β δ j z=piece n J L β δ j (retain n (k+1) z) := by
  cases j with
  | zero => exact approximation_prefix_value_next n J k L β δ τ hβ hτ hτβ hδ 0 z hz
  | succ j =>
    simp only [piece]
    rw [approximation_prefix_value_next n J k L β δ τ hβ hτ hτβ hδ (j+1) z hz,
      approximation_prefix_value_next n J k L β δ τ hβ hτ hτβ hδ j z hz]

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def activeCutCounts (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (i : Fin (P.macroNode.n+1)) : ℕ :=
  if i.val≤r then counts i+1 else 0

def cutSelectedResidual (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.cutSelector r i z.fst*
    residual P.n P.L P.β (P.cutMicroCoordinates (P.activeCutCounts r counts) i z.snd)

def cutSelectedPiece (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (j : ℕ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),P.cutSelector r i z.fst*
    piece P.n P.J P.L P.β P.δ j (P.cutMicroCoordinates (P.activeCutCounts r counts) i z.snd)

def activeLowerCut (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  lowerBase P.μ P.L q+P.μ/(2*P.L^2)*(P.cutSelectedResidual r counts (pack q.fst.fst q.snd.fst))^2-
    P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.cutSelectedPiece r counts j (pack q.fst.fst q.snd.fst)*
      PolishedLiteralCompensated.normal (P.w j) q.snd.snd)

theorem cutSelectedResidual_eq (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτβ : τ≤P.β/4) (z : Joint X U)
    (hx : ∀ l : Fin (P.macroNode.n+1),r≤l.val → |P.macroNode.coordinates z.fst l|≤P.macroNode.width/4)
    (hu : ∀ (i : Fin (P.macroNode.n+1)) (l : Fin (P.n+1)),counts i≤l.val → |P.coordinates i z.snd l|≤τ) :
    P.selectedResidual z=P.cutSelectedResidual r counts z := by
  unfold selectedResidual cutSelectedResidual microResidual
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val≤r
  · rw [P.cutSelector_eq r hb z.fst hx i,residual_prefix_value P.n (counts i) P.L P.β hβ
      (P.coordinates i z.snd) (fun l hl => (hu i l hl).trans hτβ)]
    simp only [cutMicroCoordinates,activeCutCounts,if_pos hi]
  · have hsel : wrappedSelector P.macroNode i z.fst=0 :=
      selector_future_zero P.macroNode.n r i (by omega) (P.macroNode.width⁻¹ • P.macroNode.coordinates z.fst)
        (fun l hl => ZeroChainResidualScaled.scaled_coordinate_small _ hb _ l (hx l hl))
    rw [hsel,zero_mul,← P.cutSelector_eq r hb z.fst hx i,hsel,zero_mul]

theorem cutSelectedPiece_eq (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hδ : ∀ j,j<P.J → τ≤P.δ j) (j : ℕ) (z : Joint X U)
    (hx : ∀ l : Fin (P.macroNode.n+1),r≤l.val → |P.macroNode.coordinates z.fst l|≤P.macroNode.width/4)
    (hu : ∀ (i : Fin (P.macroNode.n+1)) (l : Fin (P.n+1)),counts i≤l.val → |P.coordinates i z.snd l|≤τ) :
    P.selectedPiece j z=P.cutSelectedPiece r counts j z := by
  unfold selectedPiece cutSelectedPiece microPiece
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val≤r
  · rw [P.cutSelector_eq r hb z.fst hx i,piece_prefix_value_next P.n P.J (counts i) P.L P.β P.δ τ
      hβ hτ hτβ hδ j (P.coordinates i z.snd) (hu i)]
    simp only [cutMicroCoordinates,activeCutCounts,if_pos hi]
  · have hsel : wrappedSelector P.macroNode i z.fst=0 :=
      selector_future_zero P.macroNode.n r i (by omega) (P.macroNode.width⁻¹ • P.macroNode.coordinates z.fst)
        (fun l hl => ZeroChainResidualScaled.scaled_coordinate_small _ hb _ l (hx l hl))
    rw [hsel,zero_mul,← P.cutSelector_eq r hb z.fst hx i,hsel,zero_mul]

theorem activeLowerCut_value (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (q : FullMeanSpace (X:=X) (U:=U)) (hq : P.BlindBox r counts τ q) :
    P.sourceLower q=P.activeLowerCut r counts q := by
  have hformula : P.sourceLower q=lowerBase P.μ P.L q+
      P.μ/(2*P.L^2)*(P.selectedResidual (pack q.fst.fst q.snd.fst))^2-
      P.μ/P.L*(∑ j ∈ Finset.range (P.J+1),P.selectedPiece j (pack q.fst.fst q.snd.fst)*
        PolishedLiteralCompensated.normal (P.w j) q.snd.snd) := by
    rw [P.sourceLower_split,P.sourcePerturbation_eq]
    have he : fullLowerEmbed q=PolishedLiteralCompensated.pack _ (pack q.fst.fst q.snd.fst) q.snd.snd 0 := rfl
    change lowerBase P.μ P.L q+P.data.perturbation (fullLowerEmbed q)=_
    rw [he]
    simp only [PolishedLiteralCompensated.Data.perturbation,Parameters.data,
      PolishedLiteralCompensated.uProj_pack,PolishedLiteralCompensated.sProj_pack]
    ring
  rw [hformula]
  unfold activeLowerCut
  rw [P.cutSelectedResidual_eq r counts τ hb hβ hτβ (pack q.fst.fst q.snd.fst)
    (fun l hl => (hq.1 l hl).le) (fun i l hl => (hq.2 i l hl).le)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [P.cutSelectedPiece_eq r counts τ hb hβ hτ hτβ hδ j (pack q.fst.fst q.snd.fst)
    (fun l hl => (hq.1 l hl).le) (fun i l hl => (hq.2 i l hl).le)]

/-- Exact full active lower reply uses only the known older blocks and
one next column of the eligible block; every future block is cut to zero. -/
theorem activeLowerCut_gradient (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (q : FullMeanSpace (X:=X) (U:=U)) (hq : P.BlindBox r counts τ q) :
    gradient P.sourceLower q=gradient (P.activeLowerCut r counts) q := by
  have he : P.sourceLower=ᶠ[𝓝 q] P.activeLowerCut r counts := by
    filter_upwards [(P.blindBox_isOpen r counts τ).mem_nhds hq] with z hz
    exact P.activeLowerCut_value r counts τ hb hβ hτ hτβ hδ z hz
  simp only [gradient,he.fderiv_eq]

end Parameters
end Bilevel.PolishedLiteral
