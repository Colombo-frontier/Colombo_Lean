import RationalUniformStep254

noncomputable section
namespace Paper254

/-- A logarithmic precision schedule for a linear plus square-root error
envelope. Its magnitude bound is an input about explicit coefficients,
not an assumed approximation guarantee. -/
theorem explicit_sqrt_error_budget (A B C : ℝ) (k s : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (hAk : A≤(2:ℝ)^k) (hBk : B≤(2:ℝ)^k) (hCk : C≤((2:ℝ)^k)^2) :
    A*((2:ℝ)^(2*s+4*k+4))⁻¹+
      B*Real.sqrt (C*((2:ℝ)^(2*s+4*k+4))⁻¹)≤((2:ℝ)^s)⁻¹ := by
  let x : ℝ := ((2:ℝ)^(2*s+4*k+4))⁻¹
  let q : ℝ := (2:ℝ)^s
  let K : ℝ := (2:ℝ)^k
  have hK : 1≤K := one_le_pow₀ (by norm_num)
  have hq : 1≤q := one_le_pow₀ (by norm_num)
  have hx : x=1/(16*q^2*K^4) := by
    dsimp [x,q,K]
    simp only [pow_add,pow_mul',inv_eq_one_div]
    congr 1
    ring
  have hroot : Real.sqrt (C*x)≤1/(4*q*K) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · dsimp [q,K]; positivity
    · rw [hx,div_pow]
      have hbound : C/(16*q^2*K^4)≤K^2/(16*q^2*K^4) :=
        div_le_div_of_nonneg_right hCk (by dsimp [q,K]; positivity)
      calc
        _ = C/(16*q^2*K^4) := by ring
        _ ≤ K^2/(16*q^2*K^4) := hbound
        _ = _ := by dsimp [q,K]; field_simp; ring
  change A*x+B*Real.sqrt (C*x)≤q⁻¹
  have hfirst : A*x≤1/(4*q) := by
    rw [hx]
    have hAx := mul_le_mul_of_nonneg_right hAk (show 0≤1/(16*q^2*K^4) by dsimp [q,K]; positivity)
    apply hAx.trans
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by dsimp [q,K]; positivity) (by dsimp [q]; positivity)).mpr
    have hK3 : K≤K^4 := by nlinarith [sq_nonneg (K-1),sq_nonneg (K^2-1)]
    have hq2 : q≤q^2 := by nlinarith
    have hh := mul_le_mul hK3 hq2 (by linarith) (by positivity : 0≤K^4)
    nlinarith
  have hsecond : B*Real.sqrt (C*x)≤1/(4*q) := by
    have hh := mul_le_mul hBk hroot (Real.sqrt_nonneg _) (by positivity)
    apply hh.trans_eq
    dsimp [K,q]
    field_simp
  have he : 1/(4*q)+1/(4*q)≤q⁻¹ := by
    dsimp [q]
    field_simp
    <;> norm_num
  exact (add_le_add hfirst hsecond).trans he

end Paper254
#print axioms Paper254.explicit_sqrt_error_budget
