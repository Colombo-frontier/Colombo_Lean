import Bilevel.EndpointTransportVirtualJetRestriction
import Bilevel.EndpointTransportSourceCompletion

/-! Concrete network-prefix jets from the same source family in one finite
completed ambient space. Source and target endpoint counts may differ. No
desired prefix contraction or regularity is assumed. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportNetwork ChiTreeProgress ChiHierarchyIndex EndpointTransportMatrix
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem source_prefix_completion_jets
    {n D J s : ℕ} (macroN : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hmDim : macroN+1≤D)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
    (macroFrame : Space macroN →ₗᵢ[ℝ] Block D)
    (old : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block D)
    (P : ChiFine.Parameters) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ)
    (net : Latent (n+1) D) (q : Index n → ℕ) (rM : ℕ)
    (macroColumns : Fin (macroN+1) → Block D)
    (hmGram : PrefixGram macroN rM macroColumns)
    (columns : ∀ j,List ℕ → Fin (sourceChainIndex cn (ratios j) (resolutions j)+1) → Block D)
    (hGram : ∀ j I,PrefixGram (sourceChainIndex cn (ratios j) (resolutions j))
      (canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q (Fin.last (n+1))) j I) (columns j I))
    (sourceColumns targetColumns : ∀ j,List ℕ → Fin (sourceChainIndex cn (ratios j) (resolutions j)+1) → Physical n D)
    (hs : ∀ I k,k.val<canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q 0) J I →
      sourceColumns J I k=endpointFrame (physicalRotations net)
        (canonicalTerminalFrame (sourceCounts macroN cn ratios resolutions) (J+1) hT net I) 0 (basis k))
    (ht : ∀ I k,k.val<canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q (Fin.last (n+1))) J I →
      targetColumns J I k=endpointFrame (physicalRotations net)
        (canonicalTerminalFrame (sourceCounts macroN cn ratios resolutions) (J+1) hT net I) (Fin.last (n+1)) (basis k))
    (k : ℕ) (hk : k≤3) (C : ℝ)
    (hcomplete : ∀ (Q : Rotations n (completionDimension D D))
      (U : Space macroN →ₗᵢ[ℝ] Block (completionDimension D D))
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block (completionDimension D D)),
      ContDiff ℝ 3 (physicalHierarchyExtension Q (ChiOuter.sourceMacroNode macroN initial Km U)
        (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V) P J s coarseIndex radialIndex fineIndex ρ R dn) ∧
      ∀ z,‖iteratedFDeriv ℝ k (physicalHierarchyExtension Q (ChiOuter.sourceMacroNode macroN initial Km U)
        (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V) P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤C) :
    let M := ChiOuter.sourceMacroNode macroN initial Km macroFrame
    let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
    let r := canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q (Fin.last (n+1)))
    let rs := canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q 0)
    ContDiff ℝ 3 (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
      rM r rs macroColumns columns sourceColumns targetColumns) ∧
    ∀ z,‖iteratedFDeriv ℝ k (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
      rM r rs macroColumns columns sourceColumns targetColumns) z‖≤C := by
  let counts := sourceCounts macroN cn ratios resolutions
  let r := canonicalCounter counts J (q (Fin.last (n+1)))
  let rs := canonicalCounter counts J (q 0)
  let M := ChiOuter.sourceMacroNode macroN initial Km macroFrame
  let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
  let VM := completedMacroFrame macroN D hmDim rM macroColumns hmGram
  let V := completedHierarchyFamily counts J D hdim hT r columns hGram
  let BI := completionBlockInclusion D D
  obtain ⟨Q,hQ⟩ := network_completed_rotations_exist (capacity counts (J+1) 0) hT net q
  have hm : ∀ a,(nodeWithFrame M VM).coordinates (BI a)=readout M.n rM M.radius macroColumns a := by
    intro a
    exact completedMacroFrame_coordinates macroN D hmDim rM macroColumns hmGram M.radius a
  have hc : ∀ j I,j<J → ∀ u,(geometryWithFrames G V j I).coordinates (BI u)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) u := by
    intro j I hj u
    exact completedSource_ordinary_coordinates macroN J cn ratios resolutions hdim hT r columns hGram
      initial weight A Kminus ζ CR old j hj I u
  have hp : ∀ I u,physicalCoordinates Q (geometryWithFrames G V J I) (physicalMap BI u)=
      prefixPhysicalCoordinatesAt (G J I) (rs J I) (r J I) (sourceColumns J I) (targetColumns J I) u := by
    intro I u
    exact completedSource_physical_coordinates macroN J cn ratios resolutions hdim hT r columns hGram
      initial weight A Kminus ζ CR old net q Q hQ I (sourceColumns J I) (targetColumns J I) (hs I) (ht I) u
  have hb := hcomplete Q VM V
  exact prefix_physicalHierarchyExtension_jets M VM G V Q P rM r rs macroColumns columns
    sourceColumns targetColumns BI BI hm hc hp coarseIndex radialIndex fineIndex ρ R dn hb.1 k hk C hb.2

end Bilevel.EndpointTransportResponse
