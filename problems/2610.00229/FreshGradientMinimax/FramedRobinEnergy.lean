import FreshGradientMinimax.AcceleratedCapControl
import FreshGradientMinimax.FrameSolve

/-! The E edge energy in arbitrary ambient dual dimension. Only the edge
arguments read frame coordinates; no ambient norm is replaced by a projection. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

def framedRobinEnergy (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : ℝ :=
  robinMultiEnergy n k δ u (frameCoordinates V y)

def framedRobinGradientU (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : Euclid (k * 2 + 1) :=
  robinMultiGradientU n k δ u (frameCoordinates V y)

def framedRobinGradientY (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : Euclid dy :=
  V (robinMultiGradientY n k δ u (frameCoordinates V y))

theorem framedRobinEnergy_hasFDerivAt_u {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => framedRobinEnergy V δ v y) (innerSL ℝ (framedRobinGradientU V δ u y)) u :=
  robinMultiEnergy_hasFDerivAt_u n k hδ u _

theorem framedRobinEnergy_hasFDerivAt_y {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (framedRobinEnergy V δ u) (innerSL ℝ (framedRobinGradientY V δ u y)) y := by
  have h := (robinMultiEnergy_hasFDerivAt_y n k hδ u (frameCoordinates V y)).comp y
    (frameCoordinates V).hasFDerivAt
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply, framedRobinGradientY]
  exact V.toContinuousLinearMap.adjoint_inner_right _ z

theorem framedRobinEnergy_joint_contDiff {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid dy => framedRobinEnergy V δ z.1 z.2) := by
  let A : Joint (k * 2 + 1) dy →L[ℝ] Joint (k * 2 + 1) (k * (n + 2)) :=
    (ContinuousLinearMap.fst ℝ (Euclid (k * 2 + 1)) (Euclid dy)).prod
      ((frameCoordinates V).comp (ContinuousLinearMap.snd ℝ (Euclid (k * 2 + 1)) (Euclid dy)))
  have h := (robinMultiEnergy_joint_contDiff n k hδ).comp_continuousLinearMap (g := A)
  simpa only [A, Function.comp_def, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, framedRobinEnergy] using h

theorem framedRobinEnergy_convex_y {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    ConvexOn ℝ Set.univ (framedRobinEnergy V δ u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (robinMultiEnergy_convex_y n k hδ u).2 (Set.mem_univ (frameCoordinates V x))
    (Set.mem_univ (frameCoordinates V y)) ha hb hab
  simpa only [framedRobinEnergy, map_add, map_smul] using h

theorem framedRobinEnergy_bounds (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    0 ≤ framedRobinEnergy V δ u y ∧ framedRobinEnergy V δ u y ≤ 2000 * (k + 1 : ℕ) + 5 * ‖y‖ ^ 2 := by
  have h := robinMultiEnergy_bounds hn hδ u (frameCoordinates V y)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (frameCoordinates_norm_bound V y) 2
  exact ⟨h.1, h.2.trans (by linarith only [hs])⟩

theorem framedRobinGradientU_norm (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedRobinGradientU V δ u y‖ ≤ 14000 * Real.sqrt (k + 1 : ℕ) :=
  robinMultiGradientU_norm hn hδ u _

theorem framedRobinGradientU_norm_radius (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedRobinGradientU V δ u y‖ ≤ 14 * acceleratedDualRadius n k :=
  robinMultiGradientU_norm_radius hn hδ u _

theorem framedRobinGradientY_norm_input (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedRobinGradientY V δ u y‖ ≤ 4 * ‖y‖ + 120 * Real.sqrt (k + 1 : ℕ) := by
  rw [framedRobinGradientY, V.norm_map]
  have h := robinMultiGradientY_norm_input hn hδ u (frameCoordinates V y)
  have hc := frameCoordinates_norm_bound V y
  linarith only [h, hc]

theorem framedRobinGradientU_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedRobinGradientU V δ u y - framedRobinGradientU V δ v y‖ ≤ 10 ^ 4 * ‖u - v‖ :=
  robinMultiGradientU_difference_u hn hδ u v _

theorem framedRobinGradientU_difference_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    ‖framedRobinGradientU V δ u y - framedRobinGradientU V δ u z‖ ≤ 21 * ‖y - z‖ := by
  have h := robinMultiGradientU_difference_y hn hδ u (frameCoordinates V y) (frameCoordinates V z)
  rw [← map_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_left (frameCoordinates_norm_bound V (y - z)) (by norm_num))

theorem framedRobinGradientY_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedRobinGradientY V δ u y - framedRobinGradientY V δ v y‖ ≤ 21 * ‖u - v‖ := by
  rw [framedRobinGradientY, framedRobinGradientY, ← map_sub, V.norm_map]
  exact robinMultiGradientY_difference_u hn hδ u v _

theorem framedRobinGradientY_difference_y {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    ‖framedRobinGradientY V δ u y - framedRobinGradientY V δ u z‖ ≤ 5 * ‖y - z‖ := by
  rw [framedRobinGradientY, framedRobinGradientY, ← map_sub, V.norm_map]
  have h := robinMultiGradientY_difference_y n k hδ u (frameCoordinates V y) (frameCoordinates V z)
  rw [← map_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_left (frameCoordinates_norm_bound V (y - z)) (by norm_num))

end FreshGradientMinimax

