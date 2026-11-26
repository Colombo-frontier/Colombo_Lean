import Bilevel.ZeroChainSchedule

/-! The exponent inequalities controlling all second and third derivative
blocks, including the final piece and the J=0 case. -/

noncomputable section
namespace Bilevel.ZeroChainSchedule

def pieceExponent (θ : ℝ) (j : ℕ) : ℝ :=
  if levels θ = 0 then 0 else aExponent (min j (levels θ-1))

def amplitudeExponent (j : ℕ) : ℝ := if j = 0 then 0 else aExponent (j-1)

def pieceResolution (c β θ : ℝ) (j : ℕ) : ℝ := c*β*θ^(-pieceExponent θ j)

theorem aExponent_le_one (j : ℕ) : aExponent j ≤ 1 := by
  dsimp [aExponent]
  have h : 0 ≤ 1/(4:ℝ)^(j+1) := by positivity
  linarith

theorem bExponent_le_one (j : ℕ) : bExponent j ≤ 1 := by
  dsimp [bExponent]
  have h : 0 ≤ 1/(2*(4:ℝ)^j) := by positivity
  linarith

theorem bExponent_nonneg' (j : ℕ) : 0 ≤ bExponent j := bExponent_nonneg j

theorem a_minus_b (j : ℕ) : aExponent j-bExponent j ≤ 1/2 := by
  have hp : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  have hd : 1/(4*(4:ℝ)^j) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have he : aExponent j-bExponent j = 1/(4*(4:ℝ)^j) := by
    dsimp [aExponent,bExponent]
    rw [pow_succ]
    field_simp
    ring
  rwa [he]

theorem previous_a_bounds (j : ℕ) :
    2*aExponent j-bExponent (j+1) ≤ 1 ∧ aExponent j-bExponent (j+1) ≤ 1/2 := by
  have ha : 0 ≤ 1/(4:ℝ)^(j+1) := by positivity
  have hb : 0 ≤ 1/(2*(4:ℝ)^(j+1)) := by positivity
  have he : 1/(2*(4:ℝ)^(j+1)) = (1/(4:ℝ)^(j+1))/2 := by ring
  dsimp [aExponent,bExponent]
  rw [he]
  constructor <;> linarith

theorem amplitude_balance (j : ℕ) : 2*bExponent j-amplitudeExponent j = 1 := by
  cases j with
  | zero => norm_num [amplitudeExponent,bExponent]
  | succ j =>
    simpa only [amplitudeExponent,Nat.succ_ne_zero,if_false,Nat.succ_sub_one] using (exponent_balance j).2

theorem amplitude_difference (j : ℕ) : bExponent j-amplitudeExponent j ≤ 1/2 := by
  have hb : 1/2 ≤ bExponent j := by
    have hp : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
    have hd : 1/(2*(4:ℝ)^j) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    dsimp [bExponent]
    linarith
  linarith [amplitude_balance j]

theorem piece_exponent_bounds (θ : ℝ) (j : ℕ) (hj : j ≤ levels θ) :
    0 ≤ pieceExponent θ j ∧ pieceExponent θ j ≤ 1 ∧
      2*pieceExponent θ j-bExponent j ≤ 1 ∧ pieceExponent θ j-bExponent j ≤ 1/2 := by
  by_cases hJ : levels θ = 0
  · have hj0 : j = 0 := by omega
    subst j
    norm_num [pieceExponent,hJ,bExponent]
  · rw [pieceExponent,if_neg hJ]
    by_cases hlt : j < levels θ
    · rw [min_eq_left (by omega)]
      exact ⟨aExponent_nonneg j,aExponent_le_one j,(exponent_balance j).1.le,a_minus_b j⟩
    · have he : j = levels θ := by omega
      subst j
      have hlast : min (levels θ) (levels θ-1) = levels θ-1 := min_eq_right (Nat.sub_le _ _)
      rw [hlast]
      have hsucc : levels θ-1+1 = levels θ := by omega
      have hh := previous_a_bounds (levels θ-1)
      rw [hsucc] at hh
      exact ⟨aExponent_nonneg _,aExponent_le_one _,hh.1,hh.2⟩

theorem pieceResolution_pos (c β θ : ℝ) (hc : 0 < c) (hβ : 0 < β) (hθ : 1 ≤ θ) (j : ℕ) :
    0 < pieceResolution c β θ j := by
  have hθp : 0 < θ := by linarith
  exact mul_pos (mul_pos hc hβ) (Real.rpow_pos_of_pos hθp _)

theorem pieceResolution_le (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ)
    (j : ℕ) (hj : j ≤ levels θ) : pieceResolution c β θ j ≤ c*β := by
  have hh := Real.rpow_le_rpow_of_exponent_le hθ (neg_nonpos.mpr (piece_exponent_bounds θ j hj).1)
  simpa only [Real.rpow_zero,mul_one] using mul_le_mul_of_nonneg_left hh (mul_nonneg hc hβ)

theorem resolution_antitone (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ)
    (i j : ℕ) (hij : i ≤ j) : resolution c β θ j ≤ resolution c β θ i := by
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (Nat.add_le_add_right hij 1)
  have hd := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 4^(i+1)) hp
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hβ)
  apply Real.rpow_le_rpow_of_exponent_le hθ
  dsimp [aExponent]
  linarith

theorem pieceResolution_current (c β θ : ℝ) (j : ℕ) (hj : j < levels θ) :
    pieceResolution c β θ j = resolution c β θ j := by
  have hJ : levels θ ≠ 0 := by omega
  have hm : min j (levels θ-1) = j := min_eq_left (by omega)
  simp only [pieceResolution,pieceExponent,if_neg hJ,hm,resolution]

theorem pieceResolution_previous (c β θ : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hθ : 1 ≤ θ)
    (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ levels θ) :
    pieceResolution c β θ j ≤ resolution c β θ (j-1) := by
  have hJ : levels θ ≠ 0 := by omega
  change c*β*θ^(-(if levels θ = 0 then 0 else aExponent (min j (levels θ-1)))) ≤ _
  rw [if_neg hJ]
  apply resolution_antitone c β θ hc hβ hθ
  exact le_min (Nat.sub_le _ _) (by omega)

theorem weighted_power_ratio (c θ a b : ℝ) (hc : c ≠ 0) (hθ : 0 < θ) :
    (c*θ^(-b))/(c*θ^(-a))^2 = θ^(2*a-b)/c := by
  rw [show 2*a-b = (-b)-((-a)+(-a)) by ring,Real.rpow_sub hθ,Real.rpow_add hθ]
  field_simp
  ring

theorem power_ratio (c θ a b : ℝ) (hc : c ≠ 0) (hθ : 0 < θ) :
    (c*θ^(-b))/(c*θ^(-a)) = θ^(a-b) := by
  rw [show a-b = (-b)-(-a) by ring,Real.rpow_sub hθ]
  field_simp
  ring

theorem reciprocal_power (c θ a : ℝ) (hc : c ≠ 0) (hθ : 0 < θ) :
    1/(c*θ^(-a)) = θ^a/c := by
  rw [Real.rpow_neg hθ.le]
  field_simp

theorem amplitude_power_ratio (c θ a b : ℝ) (hθ : 0 < θ) :
    θ^(-a)/(c*θ^(-b))^2 = θ^(2*b-a)/c^2 := by
  rw [show 2*b-a = (-a)-((-b)+(-b)) by ring,Real.rpow_sub hθ,Real.rpow_add hθ]
  ring

/-- Normalized third derivative block weights. Multiplication by μ/L and
the proved piece budgets gives a numerical multiple of μθ. -/
theorem third_block_weights (c θ : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ)
    (j : ℕ) (hj : j ≤ levels θ) :
    width c 1 θ j/(pieceResolution c 1 θ j)^2 ≤ θ/c ∧
      1/pieceResolution c 1 θ j ≤ θ/c ∧
      1/width c 1 θ j ≤ θ/c ∧
      θ^(-amplitudeExponent j)/(width c 1 θ j)^2 = θ/c^2 := by
  have hθp : 0 < θ := by linarith
  have he := piece_exponent_bounds θ j hj
  simp only [width,pieceResolution,mul_one]
  rw [weighted_power_ratio c θ _ _ hc.ne' hθp,reciprocal_power c θ _ hc.ne' hθp,
    reciprocal_power c θ _ hc.ne' hθp,amplitude_power_ratio c θ _ _ hθp,amplitude_balance,Real.rpow_one]
  refine ⟨?_,?_,?_,rfl⟩
  · exact div_le_div_of_nonneg_right (by simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hθ he.2.2.1)) hc.le
  · exact div_le_div_of_nonneg_right (by simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hθ he.2.1)) hc.le
  · exact div_le_div_of_nonneg_right (by simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hθ (bExponent_le_one j))) hc.le

theorem second_block_weights (c θ : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ)
    (j : ℕ) (hj : j ≤ levels θ) :
    width c 1 θ j/pieceResolution c 1 θ j ≤ Real.sqrt θ ∧
      θ^(-amplitudeExponent j)/width c 1 θ j ≤ Real.sqrt θ/c := by
  have hθp : 0 < θ := by linarith
  have he := piece_exponent_bounds θ j hj
  simp only [width,pieceResolution,mul_one]
  constructor
  · rw [power_ratio c θ _ _ hc.ne' hθp,Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hθ he.2.2.2
  · have hid : θ^(-amplitudeExponent j)/(c*θ^(-bExponent j)) = θ^(bExponent j-amplitudeExponent j)/c := by
      rw [show bExponent j-amplitudeExponent j = (-amplitudeExponent j)-(-bExponent j) by ring,
        Real.rpow_sub hθp]
      ring
    rw [hid,Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hθ (amplitude_difference j)) hc.le

end Bilevel.ZeroChainSchedule
