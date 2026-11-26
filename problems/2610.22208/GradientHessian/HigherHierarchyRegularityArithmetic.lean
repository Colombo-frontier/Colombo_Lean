import GradientHessian.HigherHierarchyRegularityForcing
import GradientHessian.RegularityArithmetic

/-! Source-scale arithmetic for the actual residual recurrence. All
constants depend only on the fixed source radius multiplier K. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open CouplingCost
open scoped BigOperators

def residualValueBound (m : ℕ) (K : ℝ) (t : ℕ) : ℝ :=
  energy m K t + Leaf.leafJetConstant*(m+1:ℝ)^3

def newAmplitude (m : ℕ) (K : ℝ) (t : ℕ) : ℝ :=
  8*weightConstant*residualValueBound m K t + offsetConstant*spacing m K t +
    27*couplingConstant*radius m K t + 8*profileConstant*width m t

def amplitudeConstant (K : ℝ) : ℝ :=
  8*weightConstant*Leaf.leafJetConstant + (8*weightConstant+offsetConstant)*energyConstant K +
    (768*offsetConstant+27*couplingConstant)*(2*K) + 16*profileConstant

theorem amplitudeConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < amplitudeConstant K := by
  have hw := weightConstant_pos
  have ho := offsetConstant_pos
  have hc := couplingConstant_pos
  have hp := profileConstant_pos
  have he := energyConstant_pos hK
  have hl := Leaf.leafJetConstant_pos
  unfold amplitudeConstant
  positivity

theorem width_le_eight (m t : ℕ) : width m t ≤ 2*(m+1:ℝ)*8^t := by
  have hb := (FirstHeight.baseRadius_range (M := m+1) (by omega)).2.le
  push_cast at hb
  exact mul_le_mul hb (pow_le_pow_left₀ (by norm_num) (by norm_num) t)
    (by positivity) (by positivity)

theorem radius_le_eight (m : ℕ) {K : ℝ} (hK : 0 ≤ K) (t : ℕ) :
    radius m K t ≤ 2*K*(m+1:ℝ)*8^t := by
  have hb := (FirstHeight.baseRadius_range (M := m+1) (by omega)).2.le
  push_cast at hb
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hb hK)
    (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (6:ℝ) ≤ 8) t)
    (by positivity : (0:ℝ) ≤ 6^t) (by positivity : 0 ≤ K*(2*(m+1)))
  change K*FirstHeight.baseRadius (m+1)*6^t ≤ _
  convert h using 1; ring

theorem width_lower (m t : ℕ) : (m+1:ℝ)*3^t ≤ width m t := by
  have h := (FirstHeight.baseRadius_range (M := m+1) (by omega)).1
  push_cast at h
  exact mul_le_mul_of_nonneg_right h (by positivity)

theorem newAmplitude_bound (m : ℕ) {K : ℝ} (hK : 0 ≤ K) (t : ℕ) :
    newAmplitude m K t ≤ amplitudeConstant K * ((m+1:ℝ)^3 + (m+1)*8^t) := by
  let α := 8*weightConstant*Leaf.leafJetConstant
  let β := (8*weightConstant+offsetConstant)*energyConstant K
  let γ := (768*offsetConstant+27*couplingConstant)*(2*K)
  let δ := 16*profileConstant
  have hw := weightConstant_pos.le
  have ho := offsetConstant_pos.le
  have hc := couplingConstant_pos.le
  have hp := profileConstant_pos.le
  have hα : 0 ≤ α := mul_nonneg (mul_nonneg (by norm_num) hw) Leaf.leafJetConstant_pos.le
  have hβ : 0 ≤ β := mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hw) ho) (energyConstant_pos hK).le
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hδ : 0 ≤ δ := mul_nonneg (by norm_num) hp
  have he := mul_le_mul_of_nonneg_left (energy_le m hK t)
    (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hw) ho)
  have hr := mul_le_mul_of_nonneg_left (radius_le_eight m hK t)
    (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 768) ho) (mul_nonneg (by norm_num : (0:ℝ) ≤ 27) hc))
  have hwidth := mul_le_mul_of_nonneg_left (width_le_eight m t) (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hp)
  have hraw : newAmplitude m K t ≤ α*(m+1:ℝ)^3 + (β+γ+δ)*((m+1)*8^t) := by
    dsimp [newAmplitude, residualValueBound, spacing, α, β, γ, δ]
    nlinarith
  have hrest := mul_nonneg (add_nonneg (add_nonneg hβ hγ) hδ) (by positivity : 0 ≤ (m+1:ℝ)^3)
  have hother := mul_nonneg hα (by positivity : 0 ≤ (m+1:ℝ)*8^t)
  change _ ≤ (α+β+γ+δ)*((m+1:ℝ)^3+(m+1)*8^t)
  nlinarith

theorem geometric_ratio (A B a : ℝ) (t n : ℕ) :
    A*a^t/(B*3^t)^n = A/B^n*(a/(3^n))^t := by
  have hp : (3^t:ℝ)^n = (3^n)^t := by simp only [← pow_mul, Nat.mul_comm]
  rw [mul_pow, hp, div_pow]
  ring

theorem envelope_div_one (m t : ℕ) :
    ((m+1:ℝ)^3+(m+1)*8^t)/width m t ≤ (m+1)^2*(1/3)^t+(8/3)^t := by
  have hm : (0:ℝ) < m+1 := by positivity
  apply (div_le_div_of_nonneg_left (by positivity) (mul_pos hm (by positivity)) (width_lower m t)).trans_eq
  rw [add_div]
  have h1 := geometric_ratio ((m+1:ℝ)^3) (m+1) 1 t 1
  have h2 := geometric_ratio (m+1:ℝ) (m+1) 8 t 1
  simp only [pow_one, one_pow, mul_one] at h1 h2
  rw [h1, h2]
  field_simp
  ring

theorem envelope_div_two (m t : ℕ) :
    ((m+1:ℝ)^3+(m+1)*8^t)/width m t^2 ≤ (m+1)*((1/9)^t+(8/9)^t) := by
  have hm : (0:ℝ) < m+1 := by positivity
  have hm1 : (1:ℝ) ≤ m+1 := by have h := Nat.cast_nonneg (α := ℝ) m; linarith
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (m+1)*3^t) (width_lower m t) 2
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  rw [add_div]
  have h1 := geometric_ratio ((m+1:ℝ)^3) (m+1) 1 t 2
  have h2 := geometric_ratio (m+1:ℝ) (m+1) 8 t 2
  norm_num only [one_pow, mul_one, Nat.reducePow] at h1 h2
  rw [h1, h2]
  have ha : (m+1:ℝ)^3/(m+1)^2 = m+1 := by field_simp; ring
  have hb : (m+1:ℝ)/(m+1)^2 ≤ m+1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith [sq_nonneg (m:ℝ)]
  rw [ha]
  have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ (8/9)^t)
  nlinarith

theorem envelope_div_three (m t : ℕ) :
    ((m+1:ℝ)^3+(m+1)*8^t)/width m t^3 ≤ (1/27)^t+(8/27)^t := by
  have hm : (0:ℝ) < m+1 := by positivity
  have hm1 : (1:ℝ) ≤ m+1 := by have h := Nat.cast_nonneg (α := ℝ) m; linarith
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (m+1)*3^t) (width_lower m t) 3
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  rw [add_div]
  have h1 := geometric_ratio ((m+1:ℝ)^3) (m+1) 1 t 3
  have h2 := geometric_ratio (m+1:ℝ) (m+1) 8 t 3
  norm_num only [one_pow, mul_one, Nat.reducePow] at h1 h2
  rw [h1, h2, div_self (pow_ne_zero _ hm.ne'), one_mul]
  have hb : (m+1:ℝ)/(m+1)^3 ≤ 1 := by
    apply (div_le_one (pow_pos hm 3)).mpr
    nlinarith [sq_nonneg (m:ℝ)]
  have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ (8/27)^t)
  nlinarith

theorem tasks_div_width (m t : ℕ) : (m+1:ℝ)/width m t ≤ (1/3)^t := by
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) (width_lower m t)).trans_eq
  have h := geometric_ratio (m+1:ℝ) (m+1) 1 t 1
  simpa only [pow_one, one_pow, mul_one, div_self (by positivity : (m+1:ℝ) ≠ 0), one_mul] using h

theorem first_shape_div_one (m t : ℕ) :
    ((m+1:ℝ)^2+(8/3)^t)/width m t ≤ (m+1)*((1/3)^t+(8/9)^t) := by
  have hm : (0:ℝ) < m+1 := by positivity
  have hm1 : (1:ℝ) ≤ m+1 := by have h := Nat.cast_nonneg (α := ℝ) m; linarith
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) (width_lower m t)).trans
  rw [add_div]
  have h1 := geometric_ratio ((m+1:ℝ)^2) (m+1) 1 t 1
  have h2 := geometric_ratio 1 (m+1:ℝ) (8/3) t 1
  norm_num only [pow_one, one_pow, mul_one, one_mul, show (8/3:ℝ)/3 = 8/9 by norm_num] at h1 h2
  rw [h1, h2]
  have ha : (m+1:ℝ)^2/(m+1) = m+1 := by field_simp; ring
  have hb : (1:ℝ)/(m+1) ≤ m+1 := by apply (div_le_iff₀ hm).mpr; nlinarith
  rw [ha]
  have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ (8/9)^t)
  nlinarith

theorem first_shape_div_two (m t : ℕ) :
    ((m+1:ℝ)^2+(8/3)^t)/width m t^2 ≤ (1/9)^t+(8/27)^t := by
  have hm : (0:ℝ) < m+1 := by positivity
  have hm1 : (1:ℝ) ≤ m+1 := by have h := Nat.cast_nonneg (α := ℝ) m; linarith
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (m+1)*3^t) (width_lower m t) 2
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  rw [add_div]
  have h1 := geometric_ratio ((m+1:ℝ)^2) (m+1) 1 t 2
  have h2 := geometric_ratio 1 (m+1:ℝ) (8/3) t 2
  norm_num only [one_pow, mul_one, one_mul, Nat.reducePow,
    show (8/3:ℝ)/(3^2) = 8/27 by norm_num] at h1 h2
  rw [h1, h2, div_self (pow_ne_zero _ hm.ne'), one_mul]
  have hb : (1:ℝ)/(m+1)^2 ≤ 1 := by apply (div_le_one (sq_pos_of_pos hm)).mpr; nlinarith
  have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ (8/27)^t)
  nlinarith

end GradientHessian.HigherHierarchy
