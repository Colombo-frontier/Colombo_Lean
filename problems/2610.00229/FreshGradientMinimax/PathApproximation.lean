import FreshGradientMinimax.FrameSolve
import FreshGradientMinimax.PathObjective

/-! The primal derivative of the actual capped objective is approximated by
the derivative of its actual unflattened quadratic. The cap is removed only
after proving that the true flat maximizer lies in its unchanged core. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def pathSignal {n : ℕ} (i j : Fin n) (γ x M : ℝ) : Euclid n :=
  (γ * x) • EuclideanSpace.single i 1 + M • EuclideanSpace.single j 1

theorem pathSignal_norm {n : ℕ} (i j : Fin n) {γ : ℝ} (hγ : 0 ≤ γ) (x M : ℝ) :
    ‖pathSignal i j γ x M‖ ≤ γ * |x| + |M| := by
  have h := norm_add_le ((γ * x) • EuclideanSpace.single i (1 : ℝ))
    (M • EuclideanSpace.single j (1 : ℝ))
  simpa [pathSignal, norm_smul, abs_mul, abs_of_nonneg hγ] using h

theorem pathObjective_dualMax_flat {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R)
    (x : Euclid 1) (hcore : ‖pathSignal i j (L / 8) (realCoord x) M‖ ≤ μ * R) :
    (pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).dualMax x =
      V (flatMaximizer (pathIncidence s) μ (L / 8192) δ hμ (by linarith)
        hδ (pathSignal i j (L / 8) (realCoord x) M)) := by
  have hβ : 0 ≤ L / 8192 := by
    have hL : 0 < L := by linarith
    positivity
  let b := pathSignal i j (L / 8) (realCoord x) M
  let y := flatMaximizer (pathIncidence s) μ (L / 8192) δ hμ hβ hδ b
  have hyn : ‖V y‖ ≤ R := by
    rw [V.norm_map]
    exact (flatMaximizer_norm _ hμ hβ hδ b).trans ((div_le_iff₀ hμ).mpr (by
      dsimp [b] at *; nlinarith only [hcore]))
  apply pathObjective_dualMax_of_core_root V s i j L μ d M δ R hμ hκ hs hδ hR x (V y) hyn
  rw [framedPathGradient_frame]
  have h := congrArg V (flatMaximizer_gradient_zero (pathIncidence s) hμ hβ hδ b)
  change V (b - μ • y - linearFlatGradient (pathIncidence s) (L / 8192) δ y) = V 0 at h
  simp only [map_sub, map_smul, map_zero, b, pathSignal, map_add] at h
  calc
    _ = (L / 8 * realCoord x) • V (EuclideanSpace.single i 1) + M • V (EuclideanSpace.single j 1) -
        μ • V y - V (linearFlatGradient (pathIncidence s) (L / 8192) δ y) := by abel
    _ = 0 := h

theorem pathObjective_primalGradient_flat {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R)
    (x : Euclid 1) (hcore : ‖pathSignal i j (L / 8) (realCoord x) M‖ ≤ μ * R)
    (hβ : 0 ≤ L / 8192) :
    realCoord ((pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).primalGradient x) =
      L / 4 * realCoord x + d + L / 8 *
        flatMaximizer (pathIncidence s) μ (L / 8192) δ hμ hβ hδ
          (pathSignal i j (L / 8) (realCoord x) M) i := by
  change L / 4 * realCoord x + d + L / 8 *
    ⟪V (EuclideanSpace.single i 1),
      (pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).dualMax x⟫_ℝ = _
  rw [pathObjective_dualMax_flat V s i j L μ d M δ R hμ hκ hs hδ hR x hcore,
    ← frameCoordinates_apply, frameCoordinates_frame]

theorem pathObjective_primalApproximation {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R)
    (x : Euclid 1) (hcore : ‖pathSignal i j (L / 8) (realCoord x) M‖ ≤ μ * R)
    (hβ : 0 ≤ L / 8192) :
    |realCoord ((pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).primalGradient x) -
      (L / 4 * realCoord x + d + L / 8 *
        normalInverse (pathIncidence s) μ (L / 8192) hμ hβ
          (pathSignal i j (L / 8) (realCoord x) M) i)| ≤
      (L / 8) * (2 * (L / 8192) * δ * Real.sqrt (n + 1) / μ) := by
  have hL : 0 < L := by linarith
  let b := pathSignal i j (L / 8) (realCoord x) M
  let z := flatMaximizer (pathIncidence s) μ (L / 8192) δ hμ hβ hδ b
  let q := normalInverse (pathIncidence s) μ (L / 8192) hμ hβ b
  have hc : |z i - q i| ≤ ‖z - q‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (z - q) i
  have hd : ‖z - q‖ ≤ 2 * (L / 8192) * δ * Real.sqrt (n + 1) / μ := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      flatMaximizer_quadratic_distance (pathIncidence s) hμ hβ hδ (pathIncidence_opNorm hs) b
  rw [pathObjective_primalGradient_flat V s i j L μ d M δ R hμ hκ hs hδ hR x hcore hβ]
  have he : L / 4 * realCoord x + d + L / 8 * z i -
      (L / 4 * realCoord x + d + L / 8 * q i) = L / 8 * (z i - q i) := by ring
  change |L / 4 * realCoord x + d + L / 8 * z i - (L / 4 * realCoord x + d + L / 8 * q i)| ≤ _
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < L / 8)]
  exact mul_le_mul_of_nonneg_left (hc.trans hd) (by positivity)

end FreshGradientMinimax
