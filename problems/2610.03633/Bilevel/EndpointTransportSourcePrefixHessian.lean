import Bilevel.EndpointTransportSourcePrefixJets
import Bilevel.EndpointTransportWideUniformCoreWitness

/-! Apply the dimension-uniform core clause of the calibrated wide witness
to canonical network-prefix data. The same numerical radial channels and
fine parameters are retained; no new calibration is chosen. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportNetwork ChiTreeProgress ChiHierarchyIndex EndpointTransportMatrix
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem source_prefix_hessian_of_uniform_core
    {n D J s : ℕ} (macroN : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hmDim : macroN+1≤D)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
    (macroFrame : Space macroN →ₗᵢ[ℝ] Block D)
    (old : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block D)
    (P : ChiFine.Parameters) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (dn : ℝ)
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
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN initial Km U
      let G' := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' P J s coarseIndex radialIndex fineIndex rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' P J s
        coarseIndex radialIndex fineIndex rad' R' dn) z‖≤(1:ℝ)/12) :
    let M := ChiOuter.sourceMacroNode macroN initial Km macroFrame
    let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
    let ρ := fun j => weight j*(G j []).nu
    let R := fun j => (G j []).radius
    let r := canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q (Fin.last (n+1)))
    let rs := canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q 0)
    ContDiff ℝ 3 (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
      rM r rs macroColumns columns sourceColumns targetColumns) ∧
    ∀ z,‖iteratedFDeriv ℝ 2 (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
      rM r rs macroColumns columns sourceColumns targetColumns) z‖≤(1:ℝ)/12 := by
  let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR old
  let rad := fun j => weight j*(G j []).nu
  let R := fun j => (G j []).radius
  apply source_prefix_completion_jets macroN cn ratios resolutions hmDim hdim hT initial weight
    A Kminus ζ CR Km macroFrame old P coarseIndex radialIndex fineIndex rad R dn net q rM
    macroColumns hmGram columns hGram sourceColumns targetColumns hs ht 2 (by norm_num) (1/12)
  intro Q U V
  exact hcomplete (completionDimension D D) Q U V

end Bilevel.EndpointTransportResponse
