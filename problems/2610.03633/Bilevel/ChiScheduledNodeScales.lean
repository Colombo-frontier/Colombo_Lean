import Bilevel.ChiSourcePhysicalScales
import Bilevel.ChiCoarseSourceScales

/-! Definitional bridges from actual source nodes to the physical scales
and floor lengths used in the extension ledger. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem source_high_node_scales (initial : Scale) (T η K : ℝ) (weight : ℕ → ℝ)
    (A Kminus ζ cn CR : ℝ)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η K j)) →ₗᵢ[ℝ] F)
    (hl : 0 < initial.curvature) (hT : 1 ≤ T) (_hη : 0 < η) (hcn : 0 < cn)
    (hlen : 128 ≤ cn/η^2) (j : ℕ) (I : List ℕ) :
    let D := sourceGeometry initial (sourceRatio T) (resolution η K) weight A Kminus ζ cn CR V
    (D (j+1) I).n+1 = length cn η T j ∧
    (D (j+1) I).ell = initial.curvature*curvature T (j+1) ∧
    (D (j+1) I).width = η^(j+1)*initial.width/(K*curvature T (j+1)) := by
  dsimp only
  constructor
  · change sourceChainIndex cn (sourceRatio T (j+1)) (resolution η K (j+1))+1 = _
    have hn : 128 ≤ length cn η T j := length_large hcn.le hT hlen j
    rw [sourceChainIndex,source_high_length]
    omega
  constructor
  · exact source_high_node_curvature initial (by linarith) η K j
  · exact source_parent_width initial hT hl η K (j+1)

end Bilevel.ChiExtensionCalibration
