import SecondOrder.BlockSequentialAverage

open scoped Classical

namespace SecondOrder
noncomputable section

def sequentialSmallConstant (c₂ : ℝ) : ℝ := c₂/128
def sequentialDimensionConstant (c₁ c₂ : ℝ) : ℝ := 128*(1+max (Real.log c₁) 0)/c₂

theorem sequentialSmallConstant_pos {c₂ : ℝ} (hc₂ : 0<c₂) : 0<sequentialSmallConstant c₂ := by
  unfold sequentialSmallConstant
  positivity

theorem sequentialDimensionConstant_pos {c₁ c₂ : ℝ} (hc₂ : 0<c₂) :
    0<sequentialDimensionConstant c₁ c₂ := by
  unfold sequentialDimensionConstant
  have : 0≤max (Real.log c₁) 0 := le_max_right _ _
  positivity

theorem one_le_log_sixteen : (1:ℝ)≤Real.log 16 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<4)
  have he : Real.log (16:ℝ)=2*Real.log 4 := by
    rw [show (16:ℝ)=4^2 from by norm_num,Real.log_pow]
    norm_num
  rw [he]
  norm_num at hh
  linarith

/-- Explicit constants, depending only on the fixed prior-tail constants,
make all scalar hypotheses of the general sequential bound hold. The
dimension can be real; integer block dimensions are a special case. -/
theorem sequential_scalar_conditions {c₁ c₂ κ D : ℝ} (hc₁ : 0<c₁) (hc₂ : 0<c₂) (hκ : 0<κ)
    {T N : ℕ} (hT : 0<T)
    (hD : sequentialDimensionConstant c₁ c₂*Real.log (16*(N+1:ℕ)*T)≤D) :
    0<c₁*Real.exp (-c₂*D) ∧ 0<c₂*D/2 ∧
    c₂*D/2≤Real.log (1/((N+1:ℕ)*(c₁*Real.exp (-c₂*D)))) ∧
    (((⌊sequentialSmallConstant c₂*D/κ⌋₊:ℕ):ℝ)*κ+Real.log 2)/(c₂*D/2)≤1/32 ∧
    (N+1:ℕ)*T*(c₁*Real.exp (-c₂*D))≤1/16 := by
  let B : ℝ := 1+max (Real.log c₁) 0
  let M : ℝ := (N+1:ℕ)*T
  let b : ℝ := Real.log (16*M)
  have hT' : (1:ℝ)≤T := by exact_mod_cast hT
  have hN : (1:ℝ)≤(N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hM : 1≤M := by
    simpa only [one_mul] using mul_le_mul hN hT' zero_le_one (le_trans zero_le_one hN)
  have hM₀ : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hB : 1≤B := by dsimp [B]; have := le_max_right (Real.log c₁) 0; linarith
  have hb : 1≤b := one_le_log_sixteen.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hb₀ : 0≤b := le_trans zero_le_one hb
  have hB₀ : 0≤B := le_trans zero_le_one hB
  have hprod₁ : b≤B*b := by nlinarith
  have hprod₂ : B≤B*b := by nlinarith
  have hc₁log : Real.log c₁≤B := by dsimp [B]; have := le_max_left (Real.log c₁) 0; linarith
  have hscale : 128*B*b≤c₂*D := by
    have hd := mul_le_mul_of_nonneg_left hD hc₂.le
    have he : c₂*(sequentialDimensionConstant c₁ c₂*Real.log (16*(N+1:ℕ)*T))=128*B*b := by
      dsimp [sequentialDimensionConstant,B,b,M]
      field_simp
      <;> ring
    rwa [he] at hd
  have hX : 0<c₂*D := lt_of_lt_of_le (by positivity) hscale
  have hD₀ : 0≤D := by nlinarith
  have hL : 0<c₂*D/2 := by positivity
  have hlogN : Real.log (N+1:ℕ)≤b := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    nlinarith
  have hlog2 : Real.log 2≤b := Real.log_le_log (by norm_num) (by nlinarith)
  have hlogrecip : Real.log (1/((N+1:ℕ)*(c₁*Real.exp (-c₂*D))))=
      c₂*D-Real.log c₁-Real.log (N+1:ℕ) := by
    rw [one_div,Real.log_inv,Real.log_mul (by positivity) (by positivity),
      Real.log_mul hc₁.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring
  have hcap : (((⌊sequentialSmallConstant c₂*D/κ⌋₊:ℕ):ℝ)*κ)≤c₂*D/128 := by
    have hh := Nat.floor_le (show 0≤sequentialSmallConstant c₂*D/κ from
      div_nonneg (mul_nonneg (sequentialSmallConstant_pos hc₂).le hD₀) hκ.le)
    have hi := (le_div_iff₀ hκ).mp hh
    simpa only [sequentialSmallConstant,div_mul_eq_mul_div] using hi
  refine ⟨mul_pos hc₁ (Real.exp_pos _),hL,?_,?_,?_⟩
  · rw [hlogrecip]
    nlinarith
  · apply (div_le_iff₀ hL).mpr
    nlinarith
  · have hlogall : Real.log (16*M*c₁)≤c₂*D := by
      rw [Real.log_mul (by positivity) hc₁.ne']
      change b+Real.log c₁≤c₂*D
      nlinarith
    have hexp : 16*M*c₁≤Real.exp (c₂*D) := (Real.log_le_iff_le_exp (by positivity)).mp hlogall
    have hm := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-c₂*D))
    have he : Real.exp (c₂*D)*Real.exp (-c₂*D)=1 := by rw [←Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [he] at hm
    change M*(c₁*Real.exp (-c₂*D))≤1/16
    nlinarith

end
end SecondOrder
