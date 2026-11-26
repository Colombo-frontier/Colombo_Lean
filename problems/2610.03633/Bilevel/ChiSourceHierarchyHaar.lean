import Bilevel.ChiHierarchyFrameFamily

/-! The finite prior instantiated with the manuscript's actual source
branching counts. One public finite ambient dimension accommodates the
macro frame and every level, including the total indexing fallback. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule ChiExtensionCalibration ChiRecursive ChiBoundedChain

def sourceDimension (macroN : ℕ) (cn η T Kg : ℝ) : ℕ :=
  max (macroN+1) (sourceAuxiliaryDimension cn η T Kg)

def actualCounts (macroN : ℕ) (cn η T Kg : ℝ) : ℕ → ℕ :=
  sourceCounts macroN cn (sourceRatio T) (resolution η Kg)

theorem actualCounts_inner_bound (macroN : ℕ) {cn T : ℝ} (hcn : 0 ≤ cn) (hT : 1 ≤ T)
    (η Kg : ℝ) (j : ℕ) : actualCounts macroN cn η T Kg (j+1)+1 ≤ sourceDimension macroN cn η T Kg :=
  (source_chain_size_le_auxiliary hcn hT η Kg j).trans (le_max_right _ _)

theorem actualCounts_all_bound (macroN J : ℕ) {cn T : ℝ} (hcn : 0 ≤ cn) (hT : 1 ≤ T)
    (η Kg : ℝ) (i : FrameIndex (actualCounts macroN cn η T Kg) J) :
    chainSize i+1 ≤ sourceDimension macroN cn η T Kg := by
  cases i with
  | inl _ => exact le_max_left _ _
  | inr i => exact actualCounts_inner_bound macroN hcn hT η Kg i.1.val

def sourceFamily (macroN J D : ℕ) {cn T : ℝ} (hcn : 0 ≤ cn) (hT : 1 ≤ T) (η Kg : ℝ)
    (hD : sourceDimension macroN cn η T Kg ≤ D)
    (a : Orientations (actualCounts macroN cn η T Kg) J D) :
    ∀ j, List ℕ → ChiBoundedChain.Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ]
      EuclideanGaussian.Space D :=
  sourceFrame (fun j => (actualCounts_inner_bound macroN hcn hT η Kg j).trans hD) a

theorem sourceFamily_at_node (macroN J D : ℕ) {cn T : ℝ} (hcn : 0 ≤ cn) (hT : 1 ≤ T) (η Kg : ℝ)
    (hD : sourceDimension macroN cn η T Kg ≤ D)
    (a : Orientations (actualCounts macroN cn η T Kg) J D)
    (i : Node (actualCounts macroN cn η T Kg) J) :
    sourceFamily macroN J D hcn hT η Kg hD a i.1.val (nodeList i) =
      frame (fun i => (actualCounts_all_bound macroN J hcn hT η Kg i).trans hD) a (Sum.inr i) :=
  sourceFrame_at_node _ _ a i

end Bilevel.ChiHierarchyHaar
