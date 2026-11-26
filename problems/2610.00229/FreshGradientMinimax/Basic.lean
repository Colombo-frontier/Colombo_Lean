import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Basic algebra for the paper supplied as `source/0111.tex` and the matching PDF.
All statements in this project are kernel-checked; the main oracle-complexity
theorem is NOT introduced as an axiom or as a field of a purported instance.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_add_sq_le_two (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_nonneg (u - v)
  nlinarith [norm_add_sq_real u v, norm_sub_sq_real u v, sq_nonneg ‖u - v‖]

theorem norm_smul_sq (a : ℝ) (v : E) : ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The completing-the-square inequality used in the residual gap certificate. -/
theorem inner_sub_quadratic_le {m : ℝ} (hm : 0 < m) (g d : E) :
    ⟪g, d⟫_ℝ - m / 2 * ‖d‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * m) := by
  have h := sq_nonneg ‖g - m • d‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul_sq] at h
  apply (le_div_iff₀ (by positivity : 0 < 2 * m)).mpr
  nlinarith

/-- Residual and distance localization from strong monotonicity. -/
theorem residual_controls_distance (m : ℝ) (g d : E)
    (hmono : m * ‖d‖ ^ 2 ≤ ⟪g, d⟫_ℝ) : m * ‖d‖ ≤ ‖g‖ := by
  have hcs := real_inner_le_norm g d
  by_cases hd : ‖d‖ = 0
  · simp [hd, norm_nonneg]
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd)
    nlinarith

/-- Four independently established lower bounds imply their sum, losing a factor four.
This lemma does not establish any of those four oracle lower bounds. -/
theorem four_lower_bounds {T A B C D c : ℝ}
    (hA : c * A ≤ T) (hB : c * B ≤ T)
    (hC : c * C ≤ T) (hD : c * D ≤ T) :
    (c / 4) * (A + B + C + D) ≤ T := by
  linarith

def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

structure Parameters where
  L : ℝ
  μ : ℝ
  gap : ℝ
  σ : ℝ
  G : ℝ
  ε : ℝ
  μ_pos : 0 < μ
  μ_le_L : μ ≤ L
  gap_nonneg : 0 ≤ gap
  σ_nonneg : 0 ≤ σ
  G_nonneg : 0 ≤ G
  ε_pos : 0 < ε

namespace Parameters
def κ (p : Parameters) : ℝ := p.L / p.μ
def deterministic (p : Parameters) : ℝ := Real.sqrt p.κ * p.L * p.gap / p.ε ^ 2
def stochastic (p : Parameters) : ℝ := p.κ * p.L * p.gap * p.σ ^ 2 / p.ε ^ 4
def testing (p : Parameters) : ℝ := p.κ ^ 2 * p.σ ^ 2 / p.ε ^ 2
def localization (p : Parameters) : ℝ :=
  Real.sqrt p.κ * logPlus (p.G / (p.ε * Real.sqrt p.κ))
def rate (p : Parameters) : ℝ :=
  p.deterministic + p.stochastic + p.testing + p.localization

theorem condition_ge_one (p : Parameters) : 1 ≤ p.κ := by
  exact (le_div_iff₀ p.μ_pos).mpr (by simpa using p.μ_le_L)

/-- Algebraic noise-free specialization; this is not an oracle upper/lower bound. -/
theorem noise_free_rate (p : Parameters) (hσ : p.σ = 0) :
    p.rate = p.deterministic + p.localization := by
  simp [rate, stochastic, testing, hσ]

theorem zero_localization (p : Parameters) (hG : p.G = 0) : p.localization = 0 := by
  simp [localization, hG, logPlus]
end Parameters

end FreshGradientMinimax
