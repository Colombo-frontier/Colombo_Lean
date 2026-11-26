import Bilevel.EndpointTransportPayload
import Bilevel.EndpointTransportPayloadBudgets
import Bilevel.ChiSplitFineWrapped
import Bilevel.ChiSplitFineTrace
import Bilevel.ChiLinearJetContraction

/-! Concrete physical source-only fine leaves, exact response trace, and full
mixed derivative bounds after radial compression and endpoint readout. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
open RadialWrapper ZeroChainSchedule

theorem split_piece_diagonal (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) (z : Space n) :
    ChiSplitFine.piece n J δ j (pack z z)=ChiFine.piece n J δ j z := by
  have ha (i : ℕ) : ChiSplitFine.approximation n J δ i (pack z z)=ChiFine.approximation n J δ i z := by
    simp only [ChiSplitFine.approximation,ChiFine.approximation,ChiSplitFine.flattened_diagonal]
    rfl
  cases j <;> simp only [ChiSplitFine.piece,ChiFine.piece,ha]

theorem split_pieces_diagonal (P : ChiFine.Parameters) (n j : ℕ) (z : Space n) :
    ChiSplitFine.pieces P n j (pack z z)=P.pieces n j z := by
  change P.amplitude*ChiSplitFine.piece n (levels P.θ) (resolution P.c 1 P.θ) j
    (pack (P.β⁻¹ • z) (P.β⁻¹ • z))=_
  rw [split_piece_diagonal]
  rfl

def physicalFinePiece {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) (j : ℕ) : Physical n D → ℝ :=
  ChiSplitFine.pieces P N.n j ∘ physicalCoordinates Q N

def physicalFineFrontier {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) : Physical n D → ℝ :=
  ChiSplitFine.frontier N.n P.ℓ P.β ∘ physicalCoordinates Q N

theorem physicalCoordinates_contDiff {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) :
    ContDiff ℝ 3 (physicalCoordinates Q N) :=
  (ChiSplitChain.readout (sourceReadout Q N.frame) (targetReadout Q N.frame)).contDiff.comp
    (compress_contDiff (gamma n*N.radius) 3)

theorem physicalFinePiece_contDiff {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) (j : ℕ) : ContDiff ℝ 3 (physicalFinePiece Q N P j) :=
  (ChiSplitFine.pieces_contDiff P N.n j).comp (physicalCoordinates_contDiff Q N)

theorem physicalFineFrontier_contDiff {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) : ContDiff ℝ 3 (physicalFineFrontier Q N P) :=
  (ChiSplitFine.frontier_contDiff N.n P.ℓ P.β).comp (physicalCoordinates_contDiff Q N)

theorem physical_fine_decomposition {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) (Y : Physical n D) :
    (∑ j ∈ Finset.range (levels P.θ+1),physicalFinePiece Q N P j Y)=physicalFineFrontier Q N P Y :=
  ChiSplitFine.decomposition P N.n (physicalCoordinates Q N Y)

theorem physical_fine_piece_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (P : ChiFine.Parameters) (j : ℕ) (v : Block D) :
    physicalFinePiece Q N P j (physicalResponse δ c Q v)=P.pieces N.n j (N.coordinates (gain n δ c • v)) := by
  unfold physicalFinePiece
  rw [Function.comp_apply,physical_coordinates_response,split_pieces_diagonal]

theorem physical_fine_frontier_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (P : ChiFine.Parameters) (v : Block D) :
    physicalFineFrontier Q N P (physicalResponse δ c Q v)=
      ChiFine.frontier N.n P.ℓ P.β (N.coordinates (gain n δ c • v)) := by
  unfold physicalFineFrontier
  rw [Function.comp_apply,physical_coordinates_response,ChiSplitFine.frontier_diagonal]

theorem physical_fine_piece_bounds : ∃ B : ℝ,1≤B ∧ ∀ (n D : ℕ) (Q : Rotations n D)
    (N : Node (Block D)) (P : ChiFine.Parameters),P.β≤N.radius →
    ∀ j,j≤levels P.θ → ∀ (Y : Physical n D) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalFinePiece Q N P j) Y‖≤
        B*fineScale (P.amplitude*P.θ^(-amplitudeExponent j)) (P.ℓ*P.β)
          (pieceResolution P.c P.β P.θ j) k := by
  obtain ⟨B,hB,hb⟩ := ChiSplitFine.actual_wrapped_piece_bounds
  refine ⟨B,hB,fun n D Q N P hR j hj Y k hk => ?_⟩
  have hradius : P.β≤gamma n*N.radius := hR.trans
    (le_mul_of_one_le_left (P.β_pos.le.trans hR) (gamma_range n).1)
  exact hb (Physical n D) N.n P _ (readout_norm Q N.frame).2.2 (gamma n*N.radius) hradius j hj Y k hk

end Bilevel.EndpointTransportResponse

