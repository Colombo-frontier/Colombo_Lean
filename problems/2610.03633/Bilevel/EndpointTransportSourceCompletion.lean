import Bilevel.EndpointTransportCompletedFamily
import Bilevel.TransportHierarchySourceGeometry

/-! The finite network completion is a literal source family: re-framing
preserves every numerical scale. Macro/ancestor coordinate restrictions and
the two independent terminal restrictions hold for every physical query. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation EndpointTransportMatrix ChiCarrier
  TransportHierarchy TransportNetwork ChiTreeProgress ChiHierarchyIndex ChiRecursive ChiOuter

section Reframe
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem source_macro_reframe (a : ℕ) (initial : Scale) (Km : ℝ)
    (U : Space a →ₗᵢ[ℝ] E) (V : Space a →ₗᵢ[ℝ] F) :
    nodeWithFrame (sourceMacroNode a initial Km U) V=sourceMacroNode a initial Km V := rfl

theorem source_geometry_reframe (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (A Kminus ζ cn CR : ℝ)
    (U : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] E)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] F) :
    geometryWithFrames (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U) V=
      sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V := rfl
end Reframe

section Coordinates
variable {n D : ℕ} (macroN J : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (r : ℕ → List ℕ → ℕ)
  (columns : ∀ j,List ℕ → Fin (sourceChainIndex cn (ratios j) (resolutions j)+1) → Block D)
  (hGram : ∀ j I,PrefixGram (sourceChainIndex cn (ratios j) (resolutions j)) (r j I) (columns j I))
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
  (old : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block D)

theorem completedSource_ordinary_coordinates (j : ℕ) (hj : j<J) (I : List ℕ) (x : Block D) :
    let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
    let V := completedHierarchyFamily (sourceCounts macroN cn ratios resolutions) J D hdim hT r columns hGram
    (geometryWithFrames G V j I).coordinates (completionBlockInclusion D D x)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) x :=
  completedHierarchyFamily_ordinary_coordinates (sourceCounts macroN cn ratios resolutions) J D
    hdim hT r columns hGram j hj I _ x

theorem completedSource_physical_coordinates
    (z : Latent (n+1) D) (q : Index n → ℕ) (Q : Rotations n (completionDimension D D))
    (hQ : ∀ v k,Q v (commonCompletionFrame D D (basis k))=
      completionBlockEquiv D D (completedColumn D
        (min (q v) (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0))
        (paddedNetworkColumns (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0) hT z v)
        (LinearIsometryEquiv.refl ℝ (Space D)).toLinearIsometry k))
    (I : List ℕ)
    (sourceData targetData : Fin (sourceChainIndex cn (ratios J) (resolutions J)+1) → Physical n D)
    (hs : ∀ k,k.val<canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q 0) J I →
      sourceData k=endpointFrame (physicalRotations z)
        (canonicalTerminalFrame (sourceCounts macroN cn ratios resolutions) (J+1) hT z I) 0 (basis k))
    (ht : ∀ k,k.val<canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q (Fin.last (n+1))) J I →
      targetData k=endpointFrame (physicalRotations z)
        (canonicalTerminalFrame (sourceCounts macroN cn ratios resolutions) (J+1) hT z I) (Fin.last (n+1)) (basis k))
    (Y : Physical n D) :
    let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
    let V := completedHierarchyFamily (sourceCounts macroN cn ratios resolutions) J D hdim hT r columns hGram
    physicalCoordinates Q (geometryWithFrames G V J I) (physicalMap (completionBlockInclusion D D) Y)=
      prefixPhysicalCoordinatesAt (G J I)
        (canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q 0) J I)
        (canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q (Fin.last (n+1))) J I)
        sourceData targetData Y := by
  let counts := sourceCounts macroN cn ratios resolutions
  let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
  let V := completedHierarchyFamily counts J D hdim hT r columns hGram
  have hV : V J I=(commonCompletionFrame D D).comp (canonicalCompletionFrame counts J D hT I) :=
    completedHierarchyFamily_terminal counts J D hdim hT r columns hGram I
  have hsource : WrappedChain.coordinates (G J I).n (gamma n*(G J I).radius)
      (endpointFrame Q (V J I) 0) (physicalMap (completionBlockInclusion D D) Y)=
      readout (G J I).n (canonicalCounter counts J (q 0) J I) (gamma n*(G J I).radius) sourceData Y := by
    rw [hV]
    exact canonicalCompleted_endpoint_coordinates counts J hT z q Q hQ 0 I sourceData hs _ Y
  have htarget : WrappedChain.coordinates (G J I).n (gamma n*(G J I).radius)
      (endpointFrame Q (V J I) (Fin.last (n+1))) (physicalMap (completionBlockInclusion D D) Y)=
      readout (G J I).n (canonicalCounter counts J (q (Fin.last (n+1))) J I)
        (gamma n*(G J I).radius) targetData Y := by
    rw [hV]
    exact canonicalCompleted_endpoint_coordinates counts J hT z q Q hQ (Fin.last (n+1)) I targetData ht _ Y
  change pack ((2:ℝ) • WrappedChain.coordinates (G J I).n (gamma n*(G J I).radius)
    (endpointFrame Q (V J I) 0) (physicalMap (completionBlockInclusion D D) Y))
    (WrappedChain.coordinates (G J I).n (gamma n*(G J I).radius)
      (endpointFrame Q (V J I) (Fin.last (n+1))) (physicalMap (completionBlockInclusion D D) Y))=_
  rw [hsource,htarget]
  rfl

end Coordinates
end Bilevel.EndpointTransportResponse
