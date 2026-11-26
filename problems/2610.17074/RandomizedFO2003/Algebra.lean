import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Algebraic consequences of the scales and projected gradient equations in 2003.tex.
All assumptions are explicit; no analytic or probabilistic assertion is postulated. -/

namespace RandomizedFO2003

theorem scale_identity (h γ : ℝ) (hγ : γ ≠ 0) :
    (h ^ 2 / γ) * (γ ^ 3 / h ^ 3) = γ ^ 2 / h := by
  by_cases hh : h = 0
  · simp [hh]
  · field_simp
    ring

theorem normalized_cauchy_schwarz
    (α β ρ D α₀ : ℝ) (hD : 0 < D) (hα₀ : 0 < α₀)
    (hcs : α ^ 2 ≤ β * ρ) :
    (α / α₀) ^ 2 ≤ (D * β / α₀ ^ 2) * (ρ / D) := by
  have heq : (D * β / α₀ ^ 2) * (ρ / D) = (β * ρ) / α₀ ^ 2 := by
    field_simp
    ring
  rw [heq, div_pow]
  exact div_le_div_of_nonneg_right hcs (sq_nonneg α₀)

/-- Exact elimination of the outgoing forcing, equation (eliminate), without division. -/
theorem eliminate_outgoing
    (q v c s k r t w δa δb : ℝ)
    (ha : δa = v - c * s * t - k * w)
    (hb : δb = q - c * r * t - s * w) :
    k * q = s * v + c * (k * r - s ^ 2) * t + k * δb - s * δa := by
  rw [ha, hb]
  ring

/-- The bound is independent of the magnitude of the positive outgoing forcing. -/
theorem saturation_bound
    (q v c s k r t w δa δb S K : ℝ)
    (ha : δa = v - c * s * t - k * w)
    (hb : δb = q - c * r * t - s * w)
    (hk : 1 ≤ k) (hkK : k ≤ K)
    (hs : 0 ≤ s) (hsS : s ≤ S)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ht : |t| ≤ 1) (hv : |v| ≤ 1)
    (hda : |δa| ≤ 1) (hdb : |δb| ≤ 1) :
    |q| ≤ 2 * S + 2 * K + S ^ 2 := by
  have hk0 : 0 ≤ k := by linarith
  have hS : 0 ≤ S := le_trans hs hsS
  have hK : 0 ≤ K := le_trans hk0 hkK
  have hkr : |k * r - s ^ 2| ≤ K + S ^ 2 := by
    calc
      |k * r - s ^ 2| ≤ |k * r| + |s ^ 2| := abs_sub _ _
      _ = k * r + s ^ 2 := by rw [abs_of_nonneg (mul_nonneg hk0 hr), abs_of_nonneg (sq_nonneg s)]
      _ ≤ K + S ^ 2 := by nlinarith
  have hcabs : |c| ≤ 1 := by rwa [abs_of_nonneg hc]
  have hsv : |s * v| ≤ S := by
    rw [abs_mul, abs_of_nonneg hs]
    calc
      s * |v| ≤ s * 1 := mul_le_mul_of_nonneg_left hv hs
      _ ≤ S := by simpa using hsS
  have hct : |c * (k * r - s ^ 2) * t| ≤ K + S ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      |c| * |k * r - s ^ 2| * |t| ≤ 1 * (K + S ^ 2) * 1 :=
        mul_le_mul (mul_le_mul hcabs hkr (abs_nonneg _) (by norm_num)) ht
          (abs_nonneg _) (by positivity)
      _ = K + S ^ 2 := by ring
  have hkb : |k * δb| ≤ K := by
    rw [abs_mul, abs_of_nonneg hk0]
    nlinarith [abs_nonneg δb]
  have hsa : |s * δa| ≤ S := by
    rw [abs_mul, abs_of_nonneg hs]
    nlinarith [abs_nonneg δa]
  have he := eliminate_outgoing q v c s k r t w δa δb ha hb
  have hsum : |k * q| ≤ 2 * S + 2 * K + S ^ 2 := by
    rw [he]
    calc
      |s * v + c * (k * r - s ^ 2) * t + k * δb - s * δa|
          ≤ |s * v + c * (k * r - s ^ 2) * t + k * δb| + |s * δa| := abs_sub _ _
      _ ≤ |s * v + c * (k * r - s ^ 2) * t| + |k * δb| + |s * δa| :=
        add_le_add_right (abs_add _ _) _
      _ ≤ |s * v| + |c * (k * r - s ^ 2) * t| + |k * δb| + |s * δa| := by
        linarith [abs_add (s * v) (c * (k * r - s ^ 2) * t)]
      _ ≤ 2 * S + 2 * K + S ^ 2 := by linarith
  rw [abs_mul, abs_of_nonneg hk0] at hsum
  nlinarith [abs_nonneg q]

theorem gate_activation
    (v s k φ χ' δ : ℝ) (hs : 1 ≤ s) (hk : 0 ≤ k)
    (hφ : 0 ≤ φ) (hχ : 0 ≤ χ') (hδ : |δ| ≤ 1 / 8)
    (hv : v = s + k * φ * χ' + δ) : 7 / 8 ≤ v := by
  have hout : 0 ≤ k * φ * χ' := mul_nonneg (mul_nonneg hk hφ) hχ
  have := (abs_le.mp hδ).1
  linarith

/-- Exact exponent arithmetic behind the displayed N*M rate; floor bounds and
the absolute-constant choices remain separate obligations. -/
theorem rate_factorization (ε Δ L₁ L₂ : ℝ) (hε : 0 < ε) (hL₂ : 0 < L₂) :
    (Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) *
      (L₁ ^ (1 / 2 : ℝ) * L₂ ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 4 : ℝ))) =
      Δ * L₁ ^ (1 / 2 : ℝ) * L₂ ^ (1 / 4 : ℝ) * ε ^ (-(7 / 4 : ℝ)) := by
  have he : ε ^ (-(3 / 2 : ℝ)) * ε ^ (-(1 / 4 : ℝ)) = ε ^ (-(7 / 4 : ℝ)) := by
    rw [← Real.rpow_add hε]
    norm_num
  have hL : L₂ ^ (1 / 2 : ℝ) * L₂ ^ (-(1 / 4 : ℝ)) = L₂ ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hL₂]
    norm_num
  calc
    _ = Δ * L₁ ^ (1 / 2 : ℝ) *
        (L₂ ^ (1 / 2 : ℝ) * L₂ ^ (-(1 / 4 : ℝ))) *
        (ε ^ (-(3 / 2 : ℝ)) * ε ^ (-(1 / 4 : ℝ))) := by ring
    _ = _ := by rw [he, hL]

end RandomizedFO2003
