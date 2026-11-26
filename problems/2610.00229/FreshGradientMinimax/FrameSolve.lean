import FreshGradientMinimax.FlatMaximizer
import FreshGradientMinimax.FramedPath

/-! Coordinate solutions lift through the actual orthonormal frame to the
ambient problem. In particular no restriction on the ambient optimizer is
assumed: the lifted root identifies the unique global optimizer. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

variable {n dy : ℕ}

theorem frameCoordinates_frame (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (z : Euclid n) :
    frameCoordinates V (V z) = z := by
  ext i
  rw [frameCoordinates_apply, V.inner_map_map]
  simp [EuclideanSpace.inner_single_left]

theorem framedPathOperator_frame (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (s : Fin (n + 1) → ℝ) (z : Euclid n) :
    framedPathOperator V s (V z) = pathIncidence s z := by
  simp only [framedPathOperator, ContinuousLinearMap.comp_apply, frameCoordinates_frame]

theorem framedPathOperator_adjoint (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (s : Fin (n + 1) → ℝ)
    (w : Euclid (n + 1)) : ((framedPathOperator V s)†) w = V (((pathIncidence s)†) w) := by
  simp only [framedPathOperator, ContinuousLinearMap.adjoint_comp, frameCoordinates,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]
  rfl

theorem framedPathGradient_frame (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (s : Fin (n + 1) → ℝ)
    (β δ : ℝ) (z : Euclid n) :
    framedPathGradient V s β δ (V z) = V (linearFlatGradient (pathIncidence s) β δ z) := by
  simp only [framedPathGradient, linearFlatGradient, framedPathOperator_frame,
    framedPathOperator_adjoint, map_smul]

theorem normalFrame_frame (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (s : Fin (n + 1) → ℝ)
    (μ β : ℝ) (z : Euclid n) :
    normalOperator (framedPathOperator V s) μ β (V z) = V (normalOperator (pathIncidence s) μ β z) := by
  simp only [normalOperator_apply, framedPathOperator_frame, framedPathOperator_adjoint,
    map_add, map_smul]

theorem normalFrame_inverse (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (s : Fin (n + 1) → ℝ)
    {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (b : Euclid n) :
    normalInverse (framedPathOperator V s) μ β hμ hβ (V b) =
      V (normalInverse (pathIncidence s) μ β hμ hβ b) := by
  apply normalInverse_eq_of_root
  rw [normalFrame_frame, normalInverse_right]

theorem flatMaximizer_frame (V : Euclid n →ₗᵢ[ℝ] Euclid dy) (s : Fin (n + 1) → ℝ)
    {μ β δ : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) :
    flatMaximizer (framedPathOperator V s) μ β δ hμ hβ hδ (V b) =
      V (flatMaximizer (pathIncidence s) μ β δ hμ hβ hδ b) := by
  apply flatMaximizer_eq_of_root
  have h := congrArg V (flatMaximizer_gradient_zero (pathIncidence s) hμ hβ hδ b)
  change V b - μ • V (flatMaximizer (pathIncidence s) μ β δ hμ hβ hδ b) -
    framedPathGradient V s β δ (V (flatMaximizer (pathIncidence s) μ β δ hμ hβ hδ b)) = 0
  rw [framedPathGradient_frame]
  simpa only [flatPotentialGradient, map_sub, map_smul, map_zero] using h

end FreshGradientMinimax
