import FreshGradientMinimax.PathHardFamily
import FreshGradientMinimax.PenaltyValue

/-! Global primal monotonicity and the actual gap certificate for capped
path objectives. These statements are global, beyond the comparison window. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem scalar_gradient_monotone {dy : ℕ} {L μ : ℝ} (F : NCObjective 1 dy L μ) (hL : 0 ≤ L)
    (hm : ∀ x z, L / 4 * ‖z - x‖ ^ 2 ≤ ⟪F.primalGradient z - F.primalGradient x, z - x⟫_ℝ) :
    Monotone (fun t => realCoord (F.primalGradient (realVector t))) := by
  intro x z hxz
  by_cases he : x = z
  · subst z; rfl
  have hp : 0 < z - x := sub_pos.mpr (lt_of_le_of_ne hxz he)
  have h := hm (realVector x) (realVector z)
  rw [realVector_sub, realVector_norm, sq_abs] at h
  have hi : ⟪F.primalGradient (realVector z) - F.primalGradient (realVector x), realVector (z - x)⟫_ℝ =
      (realCoord (F.primalGradient (realVector z)) - realCoord (F.primalGradient (realVector x))) * (z - x) := by
    calc
      _ = ⟪realVector (z - x), F.primalGradient (realVector z) - F.primalGradient (realVector x)⟫_ℝ := real_inner_comm _ _
      _ = _ := by rw [realVector_inner, realCoord_sub]; ring
  rw [hi] at h
  have hn : 0 ≤ L / 4 * (z - x) ^ 2 := by positivity
  have hg := (mul_nonneg_iff_of_pos_right hp).mp (hn.trans h)
  exact sub_nonneg.mp hg

theorem pathObjective_primal_monotone {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R) :
    Monotone (fun t => realCoord ((pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).primalGradient
      (realVector t))) := by
  apply scalar_gradient_monotone _ (by linarith)
  unfold pathObjective
  exact penaltyObjective_value_strongMonotone _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem pathObjective_value_gap {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    (s : Fin (n + 1) → ℝ) (i j : Fin n) (L μ d M δ R : ℝ)
    (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hs : ∀ k, |s k| ≤ 1) (hδ : 0 ≤ δ) (hR : 0 < R) :
    (pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).PrimalGapAtMost
      (2 * ‖(pathObjective V s i j L μ d M δ R hμ hκ hs hδ hR).primalGradient 0‖ ^ 2 / L) := by
  unfold pathObjective
  exact penaltyObjective_value_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem pathHardObjective_primal_monotone {n dy : ℕ} (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) :
    Monotone (fun t => realCoord ((pathHardObjective V k s L μ ε hμ hκ hε hs).primalGradient (realVector t))) := by
  unfold pathHardObjective
  exact pathObjective_primal_monotone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem pathHardObjective_value_gap {n dy : ℕ} (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (k : ℕ)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) :
    (pathHardObjective V k s L μ ε hμ hκ hε hs).PrimalGapAtMost
      (2 * ‖(pathHardObjective V k s L μ ε hμ hκ hε hs).primalGradient 0‖ ^ 2 / L) := by
  unfold pathHardObjective
  exact pathObjective_value_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end FreshGradientMinimax
