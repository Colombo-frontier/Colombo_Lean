import Bilevel.ChiSourcePhysicalScales

/-! One finite auxiliary dimension for every source level. Higher
curvature ratios vary with the level, but are uniformly at most `T`. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiBoundedChain ChiCurvatureSchedule

def sourceAuxiliaryDimension (cn η T Kg : ℝ) : ℕ :=
  max (sourceChainIndex cn 1 (1/Kg)+1) (sourceChainIndex cn T η+1)

theorem source_auxiliary_dimension_pos (cn η T Kg : ℝ) :
    0<sourceAuxiliaryDimension cn η T Kg := by
  unfold sourceAuxiliaryDimension
  have hh := le_max_left (sourceChainIndex cn 1 (1/Kg)+1) (sourceChainIndex cn T η+1)
  omega

theorem source_chain_index_zero (cn η T Kg : ℝ) :
    sourceChainIndex cn (sourceRatio T 0) (resolution η Kg 0)=sourceChainIndex cn 1 (1/Kg) := rfl

theorem source_chain_index_succ (cn η T Kg : ℝ) (j : ℕ) :
    sourceChainIndex cn (sourceRatio T (j+1)) (resolution η Kg (j+1))=
      Nat.floor (cn*(curvature T (j+1)/curvature T j)/η^2)-1 := by
  simp [sourceChainIndex,sourceRatio,resolution]

theorem source_chain_size_le_auxiliary {cn T : ℝ} (hcn : 0≤cn) (hT : 1≤T)
    (η Kg : ℝ) (j : ℕ) :
    sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤sourceAuxiliaryDimension cn η T Kg := by
  cases j with
  | zero => exact le_max_left _ _
  | succ j =>
    apply le_trans _ (le_max_right _ _)
    simp only [resolution,show j+1≠0 by omega,ite_false]
    unfold sourceChainIndex
    have hr := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sourceRatio_le hT (j+1)) hcn) (sq_nonneg η)
    exact Nat.add_le_add_right (Nat.sub_le_sub_right (Nat.floor_mono hr) 1) 1

theorem fixed_source_chain_index_succ (cn η Kg : ℝ) (j : ℕ) :
    sourceChainIndex cn (sourceRatio 1 (j+1)) (resolution η Kg (j+1))=sourceChainIndex cn 1 η := by
  simp [sourceRatio,curvature,Real.one_rpow,resolution]

end Bilevel.ChiExtensionCalibration
