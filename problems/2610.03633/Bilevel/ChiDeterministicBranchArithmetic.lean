import Bilevel.ChiRefinementRates

/-! Fixed-factor comparisons used only after selecting actual hard families. -/
noncomputable section
namespace Bilevel.ChiRefinementRates

theorem deterministic_bounded_kappa {L θ κ Δ ε B : ℝ}
    (hL : 0≤L) (hθ : 0≤θ) (hΔ : 0≤Δ) (hκ : κ≤B) :
    deterministic L θ κ Δ ε≤Real.sqrt B*(L*(1+θ)*κ^2*Δ/ε^2) := by
  calc
    deterministic L θ κ Δ ε=Real.sqrt κ*(L*(1+θ)*κ^2*Δ/ε^2) := by unfold deterministic;ring
    _≤Real.sqrt B*(L*(1+θ)*κ^2*Δ/ε^2) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hκ) (by positivity)

theorem deterministic_bounded_theta {L θ κ Δ ε Θ : ℝ}
    (hL : 0≤L) (hΔ : 0≤Δ) (hθ : θ≤Θ) :
    deterministic L θ κ Δ ε≤(1+Θ)*(L*κ^2*Real.sqrt κ*Δ/ε^2) := by
  calc
    deterministic L θ κ Δ ε=(1+θ)*(L*κ^2*Real.sqrt κ*Δ/ε^2) := by unfold deterministic;ring
    _≤(1+Θ)*(L*κ^2*Real.sqrt κ*Δ/ε^2) :=
      mul_le_mul_of_nonneg_right (add_le_add_left hθ 1) (by positivity)

theorem fixed_factor_log_absorption {d base C a b ℓ : ℝ} {q : ℕ}
    (hd : 0≤d) (hC : 0<C) (ha : 0≤a) (hb : 0≤b)
    (hab : a≤b/C) (hbound : d≤C*base) (hlog : 1≤ℓ^q) :
    a*d/ℓ^q≤b*base := by
  calc
    a*d/ℓ^q≤a*d := div_le_self (mul_nonneg ha hd) hlog
    _≤(b/C)*d := mul_le_mul_of_nonneg_right hab hd
    _≤(b/C)*(C*base) := mul_le_mul_of_nonneg_left hbound (div_nonneg hb hC.le)
    _=b*base := by field_simp;ring

end Bilevel.ChiRefinementRates
