import Bilevel.EndpointTransportTrace
import Bilevel.EndpointTransportLower
import Bilevel.ChiSplitReadout

/-! Concrete endpoint frame readouts. Their exact response trace includes every
ambient direction, and their operator budget is independent of transport length. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiCarrier PrimitiveGeometry PartialLegendre RadialWrapper

def endpointFrame {n D r : ℕ} (Q : Rotations n D) (U : Space r →ₗᵢ[ℝ] Block D)
    (j : Index n) : Space r →ₗᵢ[ℝ] Physical n D :=
  (insertion (n+2) j).comp ((Q j).toLinearIsometry.comp U)

def sourceReadout {n D r : ℕ} (Q : Rotations n D) (U : Space r →ₗᵢ[ℝ] Block D) :
    Physical n D →L[ℝ] Space r := (2:ℝ) • (endpointFrame Q U 0).toContinuousLinearMap.adjoint

def targetReadout {n D r : ℕ} (Q : Rotations n D) (U : Space r →ₗᵢ[ℝ] Block D) :
    Physical n D →L[ℝ] Space r := (endpointFrame Q U (Fin.last (n+1))).toContinuousLinearMap.adjoint

theorem endpointFrame_inner {n D r : ℕ} (Q : Rotations n D)
    (U : Space r →ₗᵢ[ℝ] Block D) (j : Index n) (z : Space r) (Y : Physical n D) :
    ⟪endpointFrame Q U j z,Y⟫=⟪Q j (U z),Y j⟫ := by
  change ⟪insertion (n+2) j (Q j (U z)),Y⟫=_
  rw [real_inner_comm,inner_insertion_right,real_inner_comm]

theorem readout_coordinate {n D r : ℕ} (Q : Rotations n D)
    (U : Space r →ₗᵢ[ℝ] Block D) (Y : Physical n D) (i : Fin (r+1)) :
    sourceReadout Q U Y i=2*⟪Q 0 (U (basis i)),Y 0⟫ ∧
    targetReadout Q U Y i=⟪Q (Fin.last (n+1)) (U (basis i)),Y (Fin.last (n+1))⟫ := by
  have he (j : Index n) :
      (endpointFrame Q U j).toContinuousLinearMap.adjoint Y i=⟪Q j (U (basis i)),Y j⟫ := by
    rw [← inner_basis i ((endpointFrame Q U j).toContinuousLinearMap.adjoint Y)]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact endpointFrame_inner Q U j (basis i) Y
  constructor
  · change 2*((endpointFrame Q U 0).toContinuousLinearMap.adjoint Y i)=_
    rw [he]
  · exact he _

theorem readout_norm {n D r : ℕ} (Q : Rotations n D) (U : Space r →ₗᵢ[ℝ] Block D) :
    ‖sourceReadout Q U‖≤2 ∧ ‖targetReadout Q U‖≤1 ∧
    ‖ChiSplitChain.readout (sourceReadout Q U) (targetReadout Q U)‖≤3 := by
  have hs : ‖sourceReadout Q U‖≤2 := by
    rw [sourceReadout,norm_smul (2:ℝ) (endpointFrame Q U 0).toContinuousLinearMap.adjoint,
      Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
      ContinuousLinearMap.adjoint.norm_map]
    have hh := (endpointFrame Q U 0).norm_toContinuousLinearMap_le
    linarith only [hh]
  have ht : ‖targetReadout Q U‖≤1 := by
    rw [targetReadout,ContinuousLinearMap.adjoint.norm_map]
    exact (endpointFrame Q U _).norm_toContinuousLinearMap_le
  refine ⟨hs,ht,(ChiSplitChain.readout_norm_le _ _).trans ?_⟩
  linarith only [hs,ht]

theorem readout_response {n D r : ℕ} (δ c R : ℝ) (Q : Rotations n D)
    (U : Space r →ₗᵢ[ℝ] Block D) (v : Block D) :
    sourceReadout Q U (compress (gamma n*R) (physicalResponse δ c Q v))=
      U.toContinuousLinearMap.adjoint (compress R (gain n δ c • v)) ∧
    targetReadout Q U (compress (gamma n*R) (physicalResponse δ c Q v))=
      U.toContinuousLinearMap.adjoint (compress R (gain n δ c • v)) := by
  have he (i : Fin (r+1)) :
      U.toContinuousLinearMap.adjoint (compress R (gain n δ c • v)) i=
        ⟪U (basis i),compress R (gain n δ c • v)⟫ := by
    rw [← inner_basis i (U.toContinuousLinearMap.adjoint (compress R (gain n δ c • v))),
      ContinuousLinearMap.adjoint_inner_right]
    rfl
  constructor
  · ext i
    rw [(readout_coordinate Q U _ i).1,he]
    exact (response_exact_readouts δ c R Q v (U (basis i))).1
  · ext i
    rw [(readout_coordinate Q U _ i).2,he]
    exact (response_exact_readouts δ c R Q v (U (basis i))).2

theorem split_chain_response {n D r : ℕ} (δ c ell h ν R : ℝ) (Q : Rotations n D)
    (U : Space r →ₗᵢ[ℝ] Block D) (v : Block D) :
    wrapped (ν/gamma n^2) (gamma n*R) (ChiSplitChain.chain r ell h)
      (ChiSplitChain.readout (sourceReadout Q U) (targetReadout Q U)) (physicalResponse δ c Q v)=
    wrapped ν R (ChiBoundedChain.chain r ell h) U.toContinuousLinearMap.adjoint (gain n δ c • v) := by
  simp only [wrapped,ChiSplitChain.readout_apply]
  rw [(readout_response δ c R Q U v).1,(readout_response δ c R Q U v).2,
    ChiSplitChain.chain_diagonal,response_exact_bowl]

end Bilevel.EndpointTransportResponse
