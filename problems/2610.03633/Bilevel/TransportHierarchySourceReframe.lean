import Bilevel.TransportHierarchySourceGeometry
import Bilevel.ChiVirtualFrameIrrelevance

/-! Opaque record identities for public-template replacement. These keep
source scalar fields fixed without unfolding a complete gradient formula
while comparing the sampled and public geometry records. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 300000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (s s' : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)

theorem sourcePhysicalMacro_reframe (initial : Scale) (Km : ℝ) :
    sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km=
      reframeNode (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s' initial Km)
        (physicalMacroFrame hAll s) := rfl

theorem sourcePhysicalGeometry_reframe (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ) :
    sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR=
      reframeGeometry (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s' initial weight A Kminus ζ CR)
        (physicalFamily hdim hT s) := rfl

end Bilevel.TransportHierarchy
