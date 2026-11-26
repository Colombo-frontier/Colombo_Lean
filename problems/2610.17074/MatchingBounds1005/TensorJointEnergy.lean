import MatchingBounds1005.TensorChannelRows

/-!
# Exact physical noise scales in the joint normalized latent space

The squared projection energy of the normalized two-channel signal is the
sum of the two physical energies divided by their own variance scales.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.TensorJointEnergy
open GaussianVector GaussianBlockProjection TensorChannelRows AdaptiveGaussian

attribute [local irreducible] projection Submodule.orthogonalProjection

theorem normalized_projection_energy {d : ℕ}
    (V₃ : Submodule ℝ (Vec (cubicDim d))) (V₄ : Submodule ℝ (Vec (quarticDim d)))
    (σ₃ σ₄ : ℝ) (h₃ : Vec (cubicDim d)) (h₄ : Vec (quarticDim d)) :
    ‖projection (blockSpace V₃ V₄) (normalizedSignal σ₃ σ₄ h₃ h₄)‖ ^ 2 / 2 =
      ‖projection V₃ h₃‖ ^ 2 / (2 * σ₃ ^ 2) + ‖projection V₄ h₄‖ ^ 2 / (2 * σ₄ ^ 2) := by
  rw [block_projection_energy, normalizedSignal, LinearEquiv.apply_symm_apply]
  simp only [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  ring

theorem normalized_innovation_energy {d : ℕ}
    (V₃ W₃ : Submodule ℝ (Vec (cubicDim d))) (V₄ W₄ : Submodule ℝ (Vec (quarticDim d)))
    (σ₃ σ₄ : ℝ) (h₃ : Vec (cubicDim d)) (h₄ : Vec (quarticDim d)) :
    ‖projection (blockSpace W₃ W₄ ⊓ (blockSpace V₃ V₄)ᗮ)
      (normalizedSignal σ₃ σ₄ h₃ h₄)‖ ^ 2 / 2 =
      ‖projection (W₃ ⊓ V₃ᗮ) h₃‖ ^ 2 / (2 * σ₃ ^ 2) +
        ‖projection (W₄ ⊓ V₄ᗮ) h₄‖ ^ 2 / (2 * σ₄ ^ 2) := by
  rw [← blockSpace_orthogonal, blockSpace_inf]
  exact normalized_projection_energy _ _ _ _ _ _

end MatchingBounds1005.TensorJointEnergy
