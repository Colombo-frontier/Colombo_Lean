import Bilevel.ChiCanonicalSourceData
import Bilevel.ChiVirtualFrameIrrelevance

/-! A fixed public source template and the hidden canonical source have
identical numeric fields. Only the frame fields change; the disclosed
evaluator therefore uses the existing global reframe identities. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiPrefixEvaluation

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a a₀ : Orientations (sourceCounts macroN cn ratios resolutions) J dim)

theorem sourceCanonicalMacro_reframe (initial : Scale) (Km : ℝ) :
    sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km=
      reframeNode (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a₀ initial Km)
        (frame hAll a (Sum.inl ())) := rfl

theorem sourceCanonicalGeometry_reframe (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ) :
    sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR=
      reframeGeometry (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a₀ initial weight A Kminus ζ CR)
        (canonicalFamily hdim a) := rfl

end Bilevel.ChiHierarchyHaar
