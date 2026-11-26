import FreshGradientMinimax.LinearFlatEnergy

/-! The actual flat signed-path energy in an arbitrary ambient Hilbert space.
A linear isometry represents its orthonormal frame; the construction uses
the original ambient input and never clips an oracle query. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

def frameCoordinates (V : Euclid n →ₗᵢ[ℝ] E) : E →L[ℝ] Euclid n :=
  V.toContinuousLinearMap†

theorem frameCoordinates_opNorm (V : Euclid n →ₗᵢ[ℝ] E) : ‖frameCoordinates V‖ ≤ 1 := by
  rw [frameCoordinates, ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp

theorem frameCoordinates_apply (V : Euclid n →ₗᵢ[ℝ] E) (y : E) (i : Fin n) :
    frameCoordinates V y i = ⟪V (EuclideanSpace.single i 1), y⟫_ℝ := by
  have h := V.toContinuousLinearMap.adjoint_inner_right (EuclideanSpace.single i 1) y
  simpa [frameCoordinates, EuclideanSpace.inner_single_left] using h

def framedPathOperator (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ) : E →L[ℝ] Euclid (n + 1) :=
  (pathIncidence s).comp (frameCoordinates V)

theorem framedPathOperator_opNorm (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) : ‖framedPathOperator V s‖ ≤ 2 := by
  have hp := pathIncidence_opNorm hs
  have hv := frameCoordinates_opNorm V
  have h := ContinuousLinearMap.opNorm_comp_le (pathIncidence s) (frameCoordinates V)
  exact h.trans (by nlinarith [norm_nonneg (pathIncidence s), norm_nonneg (frameCoordinates V)])

def framedPathEnergy (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ) (β δ : ℝ) : E → ℝ :=
  linearFlatEnergy (framedPathOperator V s) β δ

def framedPathGradient (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ) (β δ : ℝ) : E → E :=
  linearFlatGradient (framedPathOperator V s) β δ

theorem framedPathEnergy_hasFDerivAt (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ) (β : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (y : E) :
    HasFDerivAt (framedPathEnergy V s β δ) (innerSL ℝ (framedPathGradient V s β δ y)) y :=
  linearFlatEnergy_hasFDerivAt _ β hδ y

theorem framedPathEnergy_bounds (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (y : E) :
    0 ≤ framedPathEnergy V s β δ y ∧ framedPathEnergy V s β δ y ≤ 2 * β * ‖y‖ ^ 2 :=
  ⟨linearFlatEnergy_nonneg _ hβ hδ y,
    linearFlatEnergy_upper _ hβ hδ (framedPathOperator_opNorm V hs) y⟩

theorem framedPathGradient_lipschitz (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) :
    LipschitzWith ⟨4 * β, by positivity⟩ (framedPathGradient V s β δ) :=
  linearFlatGradient_lipschitz _ hβ hδ (framedPathOperator_opNorm V hs)

theorem framedPathGradient_norm (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (y : E) : ‖framedPathGradient V s β δ y‖ ≤ 4 * β * ‖y‖ :=
  linearFlatGradient_norm_bound _ hβ hδ (framedPathOperator_opNorm V hs) y

theorem framedPathGradient_perturbation (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (y : E) :
    ‖framedPathGradient V s β δ y -
      β • ((framedPathOperator V s)†) (framedPathOperator V s y)‖ ≤
        2 * β * δ * Real.sqrt (n + 1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    linearFlatGradient_perturbation _ hβ hδ (framedPathOperator_opNorm V hs) y

end FreshGradientMinimax
