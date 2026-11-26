import Smoothness2601.OrderTradeoff

/-! Uniform elementary consequences of the actual order-dependent width. -/
noncomputable section
namespace Smoothness2601

theorem width_ratios {τ K s h : ℝ} (hτ : 0 < τ) (hK : 0 < K) (hs : 0 < s) (hh : 0 < h)
    (hl : K*s ≤ h) (hu : h ≤ K) :
    τ*h ≤ τ*K ∧ s/h ≤ 1/K ∧ s^2/(τ*h^2) ≤ 1/(τ*K^2) ∧
      s^2/(τ*h) ≤ s/(τ*K) := by
  refine ⟨mul_le_mul_of_nonneg_left hu hτ.le,?_,?_,?_⟩
  · apply (div_le_div_iff₀ hh hK).mpr
    nlinarith
  · apply (div_le_div_iff₀ (by positivity : 0 < τ*h^2) (by positivity : 0 < τ*K^2)).mpr
    have hsq : (K*s)^2 ≤ h^2 := (sq_le_sq₀ (by positivity) hh.le).mpr hl
    have hm := mul_le_mul_of_nonneg_left hsq hτ.le
    nlinarith only [hm]
  · apply (div_le_div_iff₀ (by positivity : 0 < τ*h) (by positivity : 0 < τ*K)).mpr
    have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ s*τ)
    nlinarith only [hm]

theorem sineWidth_pos {p : WithTop ℕ} {β K s : ℝ} (hp : 1 ≤ p)
    (hβ : 0 ≤ β) (hK : 0 < K) (hs : 0 < s) (hs1 : s ≤ 1) :
    0 < sineWidth p β s K :=
  (mul_pos hK hs).trans_le (sineWidth_bounds hp hβ hs hs1 hK).1

theorem sineWidth_square_lower {p : WithTop ℕ} {β K s : ℝ} (hp : 2 ≤ p)
    (hβ : 0 ≤ β) (hK : 0 < K) (hs : 0 < s) (hs1 : s ≤ 1) :
    s*K^2 ≤ ((2:ℝ)^β)^2*(sineWidth p β s K)^2 := by
  have hp1 : 1 ≤ p := (by norm_num : (1:WithTop ℕ) ≤ 2).trans hp
  have hh := sineWidth_pos hp1 hβ hK hs hs1
  have hb := sineWidth_derivative_budget hp1 hβ hs hs1 hK
    (r := 2) (show 2 ∈ availableOrders p from ⟨by omega,hp⟩)
  rw [inv_pow,← div_eq_mul_inv,div_pow] at hb
  exact (div_le_div_iff₀ (sq_pos_of_pos hh) (sq_pos_of_pos hK)).mp hb

/-- The second available derivative gives one accuracy threshold for the
extra coefficient s/(τh), uniformly over every cap p≥2. -/
theorem sineWidth_relative_small {p : WithTop ℕ} {τ β K s : ℝ} (hp : 2 ≤ p)
    (hτ : 0 < τ) (hβ : 0 ≤ β) (hK : 0 < K) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : s ≤ τ^2*K^2/((2:ℝ)^β)^2) :
    s/(τ*sineWidth p β s K) ≤ 1 := by
  have hp1 : 1 ≤ p := (by norm_num : (1:WithTop ℕ) ≤ 2).trans hp
  have hh := sineWidth_pos hp1 hβ hK hs hs1
  have hp2 : 0 < ((2:ℝ)^β)^2 := by positivity
  have hs' := (le_div_iff₀ hp2).mp hsmall
  have hw := sineWidth_square_lower hp hβ hK hs hs1
  have hm1 := mul_le_mul_of_nonneg_left hs' hs.le
  have hm2 := mul_le_mul_of_nonneg_left hw (sq_nonneg τ)
  have hsq : s^2 ≤ (τ*sineWidth p β s K)^2 := by
    apply (mul_le_mul_right hp2).mp
    nlinarith only [hm1,hm2]
  have hsval : s ≤ τ*sineWidth p β s K := (sq_le_sq₀ hs.le (by positivity)).mp hsq
  exact (div_le_one (by positivity)).mpr hsval

/-- A rational parametrization of the source choice τ=K^(-3/2): K=t²,
τ=t^(-3). It avoids any order-dependent choice of constants. -/
theorem square_cube_scales {t : ℝ} (ht : 1 ≤ t) :
    (1/t^3)*t^2 = 1/t ∧ 1/((1/t^3)*(t^2)^2) = 1/t ∧
      1/t^3 ≤ 1/t ∧ 1/t^2 ≤ 1/t := by
  have ht0 : 0 < t := by linarith
  refine ⟨by field_simp; ring,by field_simp; ring,?_,?_⟩
  · apply one_div_le_one_div_of_le ht0
    nlinarith [sq_nonneg (t-1)]
  · apply one_div_le_one_div_of_le ht0
    nlinarith

end Smoothness2601
