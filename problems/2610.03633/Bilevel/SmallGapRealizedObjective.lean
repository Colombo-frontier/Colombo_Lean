import Bilevel.SmallGapInstanceBounds
import Bilevel.SmallGapSeparation

/-! The separation and finite-gap statements apply to the actual lifted response. -/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open SmallGapProfiles SmallGapProfileBounds

variable (P : Parameters)

structure Geometry : Prop where
  radius : P.R / (P.L / P.μ) ≤ 1
  margin : (P.L / P.μ) * P.S * P.δ ≤ P.L * P.R / (2 * (P.L / P.μ))

def separationParameters (h : P.Geometry) : SmallGapSeparation.Parameters where
  κ := P.L / P.μ
  S := P.S
  δ := P.δ
  R := P.R
  L := P.L
  κ_pos := div_pos P.L_pos P.μ_pos
  S_pos := P.S_pos
  δ_pos := P.δ_pos
  R_pos := P.R_pos
  L_pos := P.L_pos
  width := P.width
  radius := h.radius
  margin := h.margin

def realizedObjective (ω x : ℝ) : ℝ := P.upper x (P.response ω x)

theorem realizedObjective_eq (h : P.Geometry) (ω : ℝ) :
    P.realizedObjective ω = (P.separationParameters h).objective ω := by
  funext x
  rw [realizedObjective, P.upper_response]
  simp only [r0, r1, SmallGapSeparation.Parameters.objective, separationParameters]
  ring

theorem realizedObjective_hasDerivAt (h : P.Geometry) (ω x : ℝ) :
    HasDerivAt (P.realizedObjective ω) ((P.separationParameters h).gradient ω x) x := by
  rw [P.realizedObjective_eq h]
  exact (P.separationParameters h).hasDerivAt_objective ω x

theorem realizedObjective_separation (h : P.Geometry) (x : ℝ) :
    2 * ((P.L / P.μ) * P.S * P.δ) ≤
      |deriv (P.realizedObjective 1) x| + |deriv (P.realizedObjective (-1)) x| := by
  rw [(P.realizedObjective_hasDerivAt h 1 x).deriv,
    (P.realizedObjective_hasDerivAt h (-1) x).deriv]
  simpa only [SmallGapSeparation.Parameters.derivative] using
    (P.separationParameters h).global_separation x

theorem realizedObjective_stationary_exists_unique (h : P.Geometry) (ω : ℝ)
    (hω : ω = 1 ∨ ω = -1) : ∃! x, deriv (P.realizedObjective ω) x = 0 := by
  rw [P.realizedObjective_eq h]
  exact (P.separationParameters h).stationary_exists_unique ω hω

theorem realizedObjective_coercive (h : P.Geometry) (ω : ℝ) :
    Filter.Tendsto (P.realizedObjective ω) (Filter.cocompact ℝ) Filter.atTop := by
  rw [P.realizedObjective_eq h]
  exact (P.separationParameters h).objective_coercive ω

theorem realizedObjective_minimum_exists (h : P.Geometry) (ω : ℝ) :
    ∃ x, ∀ y, P.realizedObjective ω x ≤ P.realizedObjective ω y := by
  rw [P.realizedObjective_eq h]
  exact (P.separationParameters h).objective_minimum_exists ω

theorem realizedObjective_gap (h : P.Geometry) (ω xstar : ℝ) (hω : ω = 1 ∨ ω = -1)
    (hmin : ∀ x, P.realizedObjective ω xstar ≤ P.realizedObjective ω x) :
    ((P.L / P.μ) * P.S * P.δ) ^ 2 / (2 * ((P.L / P.μ) ^ 2 * P.S + P.L)) ≤
      P.realizedObjective ω 0 - P.realizedObjective ω xstar ∧
    P.realizedObjective ω 0 - P.realizedObjective ω xstar ≤
      ((P.L / P.μ) * P.S * P.δ) ^ 2 / (2 * ((P.L / P.μ) ^ 2 * P.S)) := by
  rw [P.realizedObjective_eq h] at hmin ⊢
  exact (P.separationParameters h).minimum_gap_sandwich ω xstar hω hmin

end Bilevel.SmallGapInstance.Parameters
