import FreshGradientMinimax.PathHardRegions

/-! The original (unregularized primal) gap of the actual capped family,
with the paper's constant 80, uniformly over the frame and central sign. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem pathHardObjective_initial_primalGradient {n dy k : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (hk0 : 0 < k) (hkn : k ≤ n)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) :
    ‖(pathHardObjective V k s L μ ε hμ hκ hε hs).primalGradient 0‖ ≤ 49 / 8 * ε := by
  have hL : 0 < L := by linarith
  have hq := pathHardSlope_pos hL hμ n
  have hx : realCoord (0 : Euclid 1) ∈ Set.Icc (-8 * ε / pathHardSlope L μ hL hμ n) 0 := by
    simp only [realCoord_zero, Set.mem_Icc]
    exact ⟨div_nonpos_of_nonpos_of_nonneg (by linarith) hq.le, le_rfl⟩
  have ha := pathHardObjective_primalApproximation V hk0 hkn s L μ ε hμ hκ hε hs hL 0 hx
  simp only [realCoord_zero, mul_zero, zero_add] at ha
  have habs : |s| ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have h := scalar_initial_gradient_bound
    (g := fun _ => realCoord ((pathHardObjective V k s L μ ε hμ hκ hε hs).primalGradient 0)) habs hε ha
  simpa only [realCoord_norm] using h

theorem pathHardObjective_gap {n dy k : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (hk0 : 0 < k) (hkn : k ≤ n)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1) :
    (pathHardObjective V k s L μ ε hμ hκ hε hs).PrimalGapAtMost (80 * ε ^ 2 / L) := by
  have hL : 0 < L := by linarith
  have hg := pathHardObjective_initial_primalGradient V hk0 hkn s L μ ε hμ hκ hε hs
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hnum : 2 * ‖(pathHardObjective V k s L μ ε hμ hκ hε hs).primalGradient 0‖ ^ 2 ≤
      80 * ε ^ 2 := by nlinarith only [hsq, sq_nonneg ε]
  intro x
  exact (pathHardObjective_value_gap V k s L μ ε hμ hκ hε hs x).trans
    (div_le_div_of_nonneg_right hnum hL.le)

theorem lemma_B1 {n dy k : ℕ}
    (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy) (hk0 : 0 < k) (hkn : k ≤ n)
    (s L μ ε : ℝ) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hε : 0 < ε) (hs : s ^ 2 = 1)
    (hL : 0 < L) :
    let F := pathHardObjective V k s L μ ε hμ hκ hε hs
    ‖F.gradY 0 0‖ = pathHardSignal L μ ε n ∧
      F.PrimalGapAtMost (80 * ε ^ 2 / L) ∧
      F.successSet ε ⊆ {x | realCoord x ∈ pathDecisionInterval s ε (pathHardSlope L μ hL hμ n)} := by
  refine ⟨pathHardObjective_initial_residual V k s L μ ε hμ hκ hε hs,
    pathHardObjective_gap V hk0 hkn s L μ ε hμ hκ hε hs, ?_⟩
  intro x hx
  exact pathHardObjective_success_interval V hk0 hkn s L μ ε hμ hκ hε hs hL hx

end FreshGradientMinimax
