import Bilevel.ChiSourcePhysicalFullPrefix
import Bilevel.ChiSourceInverseGeometry

/-! Full disclosure for the abstract source geometry, before any physical
network family is substituted. The arrays are typed by public chain counts. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre ChiExtension
  ChiPrefixEvaluation ChiExtensionCalibration
set_option autoImplicit false
set_option maxHeartbeats 400000

variable (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
  (U : Space macroN →ₗᵢ[ℝ] Block D)
  (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block D)
  (Q : Rotations n D) (fine : ChiFine.Parameters)
  (ci ri : Fin J → Fin s) (fi : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
  (MC : Fin (macroN+1) → Block D)
  (C : ∀ j,List ℕ → Fin (sourceChainIndex cn (ratios j) (resolutions j)+1) → Block D)
  (S T : ∀ j,List ℕ → Fin (sourceChainIndex cn (ratios j) (resolutions j)+1) → Physical n D)
  (hm : ∀ k,MC k=U (basis k)) (hc : ∀ j I k,C j I k=V j I (basis k))
  (hs : ∀ I k,S J I k=endpointFrame Q (V J I) 0 (basis k))
  (ht : ∀ I k,T J I k=endpointFrame Q (V J I) (Fin.last (n+1)) (basis k))
  (hl : 0 < initial.curvature) (hw : 0 < initial.width)
  (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
  (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)

include hm hc ht hl hw hr hη hη1 hweight hζ hCR hKm in
theorem source_physical_upper_full_prefix (ν : ℝ) (hJ : 0<J) :
    let M := sourceMacroNode macroN initial Km U
    let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
    physicalUpperBase J Q M ν G J (ρ 0) (R 0)=
      prefixPhysicalUpperBase J M ν G J (ρ 0) (R 0) (macroN+1)
        (fun j _ => sourceChainIndex cn (ratios j) (resolutions j)+1) MC C T := by
  let M := sourceMacroNode macroN initial Km U
  let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
  have geo := source_inverse_geometry initial ratios resolutions weight A Kminus ζ cn CR Km macroN U V
    hl hw hr hη hη1 hweight hζ hCR hKm
  exact physicalUpperBase_full_prefix (m:=J) Q M ν G J hJ (ρ 0) (R 0) MC C T hm hc ht geo.1
    (fun I => (geo.2.2.1 0 I).1)
    (fun j I _ => (geo.2.2.1 j I).2.2.2.1)
    (fun j I _ => (geo.2.2.1 j I).2.2.2.2)

end Bilevel.EndpointTransportResponse
