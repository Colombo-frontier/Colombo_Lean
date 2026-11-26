import BlockLower254
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace Paper254

theorem lower_block_integer_parameters (m T : ℕ) (hm : 0 < m) (r : ℝ)
    (hr : 2 ≤ r) (hbudget : r*(m : ℝ)^2 ≤ T/4) :
    let K := ⌊r⌋₊
    let n := T/(K*m)
    0 < K ∧ 0 < n ∧ K*(n*m) ≤ T ∧ (T : ℝ) ≤ 2*(K*(n*m) : ℕ) ∧
    r/2 ≤ (K : ℝ) ∧ (K : ℝ) ≤ r ∧ (K : ℝ)*(m : ℝ)^2 ≤ T/4 := by
  let K := ⌊r⌋₊
  let n := T/(K*m)
  have hKlo : r/2 ≤ (K : ℝ) := by
    have hh := Nat.lt_floor_add_one r
    linarith
  have hKhi : (K : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hKr : (0 : ℝ) < K := by linarith
  have hK : 0 < K := by exact_mod_cast hKr
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hKm2 := (mul_le_mul_of_nonneg_right hKhi (sq_nonneg (m : ℝ))).trans hbudget
  have hKm : (K : ℝ)*m ≤ T/4 := by
    have hh := mul_nonneg hKr.le (show 0 ≤ (m : ℝ)^2-m by nlinarith)
    nlinarith
  have hKmNat : K*m ≤ T := by
    have ht : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    exact_mod_cast (show (K : ℝ)*m ≤ T by linarith)
  have hKmpos := Nat.mul_pos hK hm
  have hn : 0 < n := Nat.div_pos hKmNat hKmpos
  have hfit : K*(n*m) ≤ T := by
    have hh := Nat.div_mul_le_self T (K*m)
    change n*(K*m) ≤ T at hh
    nlinarith
  have hfill : (T : ℝ) ≤ 2*(K*(n*m) : ℕ) := by
    have hh := Nat.lt_mul_div_succ T hKmpos
    change T < (K*m)*(n+1) at hh
    have hn1 : 1 ≤ n := hn
    have hb : T ≤ 2*(K*(n*m)) := by nlinarith
    exact_mod_cast hb
  exact ⟨hK,hn,hfit,hfill,hKlo,hKhi,hKm2⟩

theorem lower_block_signal (m T K n : ℕ) (hm : 0 < m) (hT : 0 < T) (hK : 0 < K)
    (hfit : K*(n*m) ≤ T) (hfill : (T : ℝ) ≤ 2*(K*(n*m) : ℕ))
    (hbudget : (K : ℝ)*(m : ℝ)^2 ≤ T/4)
    (P : ℝ) (hP : 0 ≤ P) (hpath : (K : ℝ)^3*(m : ℝ)^2 ≤ T*P^2) :
    ∃ θ a : ℝ, 0 ≤ a ∧ a ≤ 1/2 ∧ (m : ℝ)*θ^2 ≤ a^2 ∧
      (n : ℝ)*θ^2 ≤ 1/32 ∧ 2*a*K ≤ P ∧
      (K : ℝ)*m/1024 ≤ ((K*(n*m) : ℕ) : ℝ)*θ^2/4 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  let θ := Real.sqrt ((K : ℝ)*m/(128*T))
  let a := Real.sqrt ((m : ℝ)*θ^2)
  have hθ : θ^2 = (K : ℝ)*m/(128*T) := Real.sq_sqrt (by positivity)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a^2 = (m : ℝ)*θ^2 := Real.sq_sqrt (by positivity)
  have hnorm : a^2 ≤ 1/512 := by
    rw [hasq,hθ, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 128*(T : ℝ) by positivity)).mpr
    nlinarith
  have hsmall : a ≤ 1/2 := by nlinarith
  have hfitr : (K : ℝ)*(n*m) ≤ T := by exact_mod_cast hfit
  have hinfo : (n : ℝ)*θ^2 ≤ 1/32 := by
    rw [hθ, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 128*(T : ℝ) by positivity)).mpr
    nlinarith
  have hmove : 2*a*K ≤ P := by
    have he : (2*a*K)^2*(128*T) = 4*(K : ℝ)^3*(m : ℝ)^2 := by
      rw [mul_pow,mul_pow,hasq,hθ]
      field_simp <;> ring
    have hb : (2*a*K)^2 ≤ P^2 := by
      apply (mul_le_mul_iff_left₀ (show 0 < 128*(T : ℝ) by positivity)).mp
      have hp : 0 ≤ (T : ℝ)*P^2 := by positivity
      nlinarith
    nlinarith
  have hrate : (K : ℝ)*m/1024 ≤ ((K*(n*m) : ℕ) : ℝ)*θ^2/4 := by
    rw [hθ]
    have hh := mul_le_mul_of_nonneg_right hfill (show 0 ≤ (K : ℝ)*m by positivity)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 128*(T : ℝ) by positivity)).mpr
    nlinarith
  exact ⟨θ,a,ha,hsmall,hasq.ge,hinfo,hmove,hrate⟩

end Paper254
#print axioms Paper254.lower_block_signal
