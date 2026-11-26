import Bilevel.EndpointTransportCompletedBlocks
import Bilevel.EndpointTransportVirtualFormula

/-! Exact global-coordinate restriction for the completed physical frames.
The ambient radial norm is preserved before both endpoint readouts, while
each endpoint retains its own independent local prefix length. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation EndpointTransportMatrix ChiCarrier ChiRecursive

theorem completed_endpoint_coordinates {n D K a : ℕ} (r : Index n → ℕ)
    (columns : Index n → Fin (K+1) → Block D) (Q : Rotations n (completionDimension D K))
    (hQ : ∀ i k,Q i (commonCompletionFrame D K (basis k))=
      completionBlockEquiv D K (completedColumn K (r i) (columns i)
        (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry k))
    (U : Space a →ₗᵢ[ℝ] Space K) (ι : Fin (a+1) → Fin (K+1))
    (hU : ∀ k,U (basis k)=basis (ι k)) (i : Index n) (count : ℕ)
    (hp : ∀ k : Fin (a+1),(ι k).val<r i ↔ k.val<count)
    (data : Fin (a+1) → Physical n D)
    (hd : ∀ k : Fin (a+1),k.val<count → data k=insertion (n+2) i (columns i (ι k)))
    (R : ℝ) (Y : Physical n D) :
    WrappedChain.coordinates a R (endpointFrame Q ((commonCompletionFrame D K).comp U) i)
      (physicalMap (completionBlockInclusion D K) Y)=readout a count R data Y := by
  ext k
  rw [ChiPrefixEvaluation.coordinates_inner,physicalMap_compress,readout_apply]
  have he : endpointFrame Q ((commonCompletionFrame D K).comp U) i (basis k)=
      endpointFrame Q (commonCompletionFrame D K) i (basis (ι k)) := by
    change insertion (n+2) i (Q i (commonCompletionFrame D K (U (basis k))))=_
    rw [hU]
    rfl
  rw [he,completed_endpoint_inner r columns Q hQ]
  by_cases hk : k.val<count
  · rw [if_pos ((hp k).mpr hk),if_pos hk,hd k hk]
    calc
      _=⟪RadialWrapper.compress R Y i,columns i (ι k)⟫ := real_inner_comm _ _
      _=⟪RadialWrapper.compress R Y,insertion (n+2) i (columns i (ι k))⟫ :=
        (inner_insertion_right (RadialWrapper.compress R Y) i (columns i (ι k))).symm
      _=_ := real_inner_comm _ _
  · rw [if_neg (fun h => hk ((hp k).mp h)),if_neg hk]

def completedPhysicalNode {D K : ℕ} (N : Node (Block D))
    (U : Space N.n →ₗᵢ[ℝ] Space K) : Node (Block (completionDimension D K)) where
  n := N.n
  ell := N.ell
  width := N.width
  receiver := N.receiver
  nu := N.nu
  force := N.force
  parentWidth := N.parentWidth
  tailRadius := N.tailRadius
  radius := N.radius
  frame := (commonCompletionFrame D K).comp U

theorem completed_physical_coordinates {n D K : ℕ} (r : Index n → ℕ)
    (columns : Index n → Fin (K+1) → Block D) (Q : Rotations n (completionDimension D K))
    (hQ : ∀ i k,Q i (commonCompletionFrame D K (basis k))=
      completionBlockEquiv D K (completedColumn K (r i) (columns i)
        (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry k))
    (N : Node (Block D)) (U : Space N.n →ₗᵢ[ℝ] Space K) (ι : Fin (N.n+1) → Fin (K+1))
    (hU : ∀ k,U (basis k)=basis (ι k)) (rs rt : ℕ)
    (hs : ∀ k : Fin (N.n+1),(ι k).val<r 0 ↔ k.val<rs)
    (ht : ∀ k : Fin (N.n+1),(ι k).val<r (Fin.last (n+1)) ↔ k.val<rt)
    (sourceColumns targetColumns : Fin (N.n+1) → Physical n D)
    (hsource : ∀ k : Fin (N.n+1),k.val<rs → sourceColumns k=insertion (n+2) 0 (columns 0 (ι k)))
    (htarget : ∀ k : Fin (N.n+1),k.val<rt → targetColumns k=
      insertion (n+2) (Fin.last (n+1)) (columns (Fin.last (n+1)) (ι k)))
    (Y : Physical n D) :
    physicalCoordinates Q (completedPhysicalNode N U) (physicalMap (completionBlockInclusion D K) Y)=
      prefixPhysicalCoordinatesAt N rs rt sourceColumns targetColumns Y := by
  have hcs := completed_endpoint_coordinates r columns Q hQ U ι hU 0 rs hs sourceColumns hsource
    (gamma n*N.radius) Y
  have hct := completed_endpoint_coordinates r columns Q hQ U ι hU (Fin.last (n+1)) rt ht targetColumns htarget
    (gamma n*N.radius) Y
  change pack ((2:ℝ) • WrappedChain.coordinates N.n (gamma n*N.radius)
      (endpointFrame Q ((commonCompletionFrame D K).comp U) 0) (physicalMap (completionBlockInclusion D K) Y))
      (WrappedChain.coordinates N.n (gamma n*N.radius)
        (endpointFrame Q ((commonCompletionFrame D K).comp U) (Fin.last (n+1)))
          (physicalMap (completionBlockInclusion D K) Y))=_
  rw [hcs,hct]
  rfl

end Bilevel.EndpointTransportResponse



