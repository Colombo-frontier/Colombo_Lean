import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The boundary below smoothness order two

This formalizes Proposition 5.1 of `2401.tex`: global positive strong
convexity is incompatible with a globally `ν`-Holder gradient when
`0 < ν < 1` on a nontrivial real Hilbert space.
-/

open scoped InnerProductSpace

namespace NoisyZO

private theorem no_linear_le_subHolder
    {μ L ν : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (_hν0 : 0 < ν) (hν1 : ν < 1)
    (hbound : ∀ r : ℝ, 0 < r → μ * r ≤ L * r ^ ν) : False := by
  let δ : ℝ := 1 - ν
  let q : ℝ := L / μ + 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hq : 1 ≤ q := by
    dsimp [q]
    have : 0 ≤ L / μ := div_nonneg hL (le_of_lt hμ)
    linarith
  let r : ℝ := q ^ δ⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq) _
  have hrδ : r ^ δ = q := by
    dsimp [r]
    exact Real.rpow_inv_rpow (le_trans zero_le_one hq) (ne_of_gt hδ)
  have hr_split : r = r ^ ν * r ^ δ := by
    calc
      r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ = r ^ (ν + δ) := by simp [δ]
      _ = r ^ ν * r ^ δ := Real.rpow_add hr ν δ
  have hνpow : 0 < r ^ ν := Real.rpow_pos_of_pos hr ν
  have hraw := hbound r hr
  have hmain : μ * (r ^ ν * r ^ δ) ≤ L * r ^ ν := by
    rw [← hr_split]
    exact hraw
  rw [hrδ] at hmain
  have hμq : μ * q = L + μ := by
    dsimp [q]
    field_simp [ne_of_gt hμ]
  have hrewrite : μ * (r ^ ν * q) = (L + μ) * r ^ ν := by
    calc
      μ * (r ^ ν * q) = (μ * q) * r ^ ν := by ring
      _ = (L + μ) * r ^ ν := by rw [hμq]
  rw [hrewrite] at hmain
  nlinarith [mul_pos hμ hνpow]

/-- The symmetric strong-convexity inequalities imply strong monotonicity of
the supplied gradient map. -/
private theorem strong_subgradient_monotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (μ : ℝ)
    (hstrong : ∀ x y,
      f x + ⟪g x, y - x⟫_ℝ + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (x y : E) :
    μ * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by
  have hxy := hstrong x y
  have hyx := hstrong y x
  rw [norm_sub_rev y x] at hxy
  calc
    μ * ‖x - y‖ ^ 2 ≤
        -(⟪g x, y - x⟫_ℝ + ⟪g y, x - y⟫_ℝ) := by
          linarith
    _ = ⟪g x - g y, x - y⟫_ℝ := by
          have hneg : ⟪g x, y - x⟫_ℝ = -⟪g x, x - y⟫_ℝ := by
            calc
              ⟪g x, y - x⟫_ℝ = ⟪g x, -(x - y)⟫_ℝ := by
                congr 1
                abel
              _ = -⟪g x, x - y⟫_ℝ := inner_neg_right (g x) (x - y)
          rw [hneg, inner_sub_left]
          ring

/-- No globally strongly convex function can have a globally sub-Lipschitz
Holder gradient on a nontrivial real Hilbert space. -/
theorem no_global_stronglyConvex_subHolder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E]
    (f : E → ℝ) (g : E → E) {μ L ν : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hstrong : ∀ x y,
      f x + ⟪g x, y - x⟫_ℝ + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (hholder : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ ^ ν) : False := by
  obtain ⟨w : E, hw⟩ := exists_ne (0 : E)
  have hwNorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let v : E := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hwNorm.ne']
  apply no_linear_le_subHolder hμ hL hν0 hν1
  intro r hr
  let x : E := r • v
  let y : E := 0
  have hxyNorm : ‖x - y‖ = r := by
    simp [x, y, norm_smul, abs_of_pos hr, hv]
  have hmono := strong_subgradient_monotone f g μ hstrong x y
  have hcauchy := real_inner_le_norm (g x - g y) (x - y)
  have hhold := hholder x y
  rw [hxyNorm] at hmono hcauchy hhold
  have hchain : μ * r ^ 2 ≤ L * r ^ ν * r := by
    calc
      μ * r ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := hmono
      _ ≤ ‖g x - g y‖ * r := hcauchy
      _ ≤ (L * r ^ ν) * r := by gcongr
  nlinarith

end NoisyZO
