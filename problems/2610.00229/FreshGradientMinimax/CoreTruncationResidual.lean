import FreshGradientMinimax.CoreCapResidual

/-! Residual estimates for actual partial gradients, including the terminal
prefix where the two scalar objectives coincide exactly. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem coreProtectedObjective_gradient_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (u : Euclid (n + 1)) (y : Euclid dy) :
    gradient (fun v => coreProtectedObjective V μ t v y) u = coreProtectedGradU V μ t u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (coreProtectedObjective_hasFDerivAt_u V hμ ht u y)).gradient

theorem truncatedCore_gradient_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t r : ℝ} (hμ : 0 < μ) (ht : 0 < t) (hr : 0 ≤ r) (hrt : r ≤ t)
    (k : Fin (n + 1)) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hy : ∀ e : Fin n, k.val ≤ e.val →
      |frameCoordinates V y (e.castAdd n)| ≤ r ∧ |frameCoordinates V y (e.natAdd n)| ≤ r) :
    ‖gradient (fun v => coreProtectedObjective V μ t v y) u -
      gradient (fun v => truncatedCoreObjective V μ t (k.val + 1) v y) u‖ ≤ 162 * (2 * μ * t) * r ∧
    ‖gradient (coreProtectedObjective V μ t u) y -
      gradient (truncatedCoreObjective V μ t (k.val + 1) u) y‖ ≤ 10 * (2 * μ * t) := by
  by_cases hk : k.val = n
  · rw [hk, truncatedCoreObjective_full]
    simp only [sub_self, norm_zero]
    constructor <;> positivity
  · have hklt : k.val < n := by omega
    let e : Fin n := ⟨k.val, hklt⟩
    have he : e.val = k.val := rfl
    have hyL := (hy e (by rfl)).1
    have hyR := (hy e (by rfl)).2
    have hU := coreProtectedCapGradU_prefix_residual V hμ ht hr e u y hu hyL hyR
    have hY := coreProtectedCapGradY_prefix_residual V hμ ht hrt e u y hu hyL hyR
    simp only [he] at hU hY
    rw [coreProtectedObjective_gradient_u V hμ ht, coreProtectedObjective_gradient_y V hμ ht]
    unfold truncatedCoreObjective
    rw [maskedCore_gradient_u V hμ ht, maskedCore_gradient_y V hμ ht]
    constructor
    · simpa only [coreProtectedGradU, maskedCoreGradU, coreSeed_prefix_gradient u hu,
        sub_sub_sub_cancel_left, norm_sub_rev] using hU
    · simpa only [coreProtectedGradY, maskedCoreGradY, sub_sub_sub_cancel_left, norm_sub_rev] using hY

theorem paperCore_gradient_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ lam r : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (hr : 0 ≤ r) (hrt : r ≤ Real.sqrt (lam / μ))
    (k : Fin (n + 1)) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hy : ∀ e : Fin n, k.val ≤ e.val →
      |frameCoordinates V y (e.castAdd n)| ≤ r ∧ |frameCoordinates V y (e.natAdd n)| ≤ r) :
    ‖gradient (fun v => paperCoreObjective V μ lam v y) u -
      gradient (fun v => paperTruncatedCore V μ lam (k.val + 1) v y) u‖ ≤
        162 * (2 * μ * Real.sqrt (lam / μ)) * r ∧
    ‖gradient (paperCoreObjective V μ lam u) y -
      gradient (paperTruncatedCore V μ lam (k.val + 1) u) y‖ ≤ 10 * (2 * μ * Real.sqrt (lam / μ)) :=
  truncatedCore_gradient_residual V hμ (Real.sqrt_pos.mpr (div_pos hlam hμ)) hr hrt k u y hu hy

end FreshGradientMinimax
