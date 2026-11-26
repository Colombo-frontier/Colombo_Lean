import RationalNewton254

namespace Paper254

def certifiedSqrt (a : ℚ) (L p : ℕ) : ℚ :=
  rationalNewton (p+2) a ((2:ℚ)^L+1) (L+p+3)

/-- An explicit stopping schedule: linear in the magnitude exponent and
requested precision. All operations of certifiedSqrt are rational. -/
theorem certifiedSqrt_error (a : ℚ) (L p : ℕ) (ha : 0 < (a:ℝ))
    (hmag : (a:ℝ) ≤ (2:ℝ)^L) :
    Real.sqrt (a:ℝ) ≤ (certifiedSqrt a L p:ℝ) ∧
      (certifiedSqrt a L p:ℝ)-Real.sqrt (a:ℝ) ≤ ((2:ℝ)^p)⁻¹ := by
  have htwo : (1:ℝ) ≤ 2^L := one_le_pow₀ (by norm_num)
  have hs : Real.sqrt (a:ℝ) ≤ (2:ℝ)^L+1 := by
    have hsq := Real.sq_sqrt ha.le
    have hnon := Real.sqrt_nonneg (a:ℝ)
    nlinarith [sq_nonneg ((2:ℝ)^L)]
  have hinit : Real.sqrt (a:ℝ) ≤ (((2:ℚ)^L+1:ℚ):ℝ) := by exact_mod_cast hs
  have hn := rationalNewton_error (p+2) a ((2:ℚ)^L+1) ha hinit (L+p+3)
  push_cast at hn
  refine ⟨hn.1,hn.2.trans ?_⟩
  have hinitial : ((2:ℝ)^L+1-Real.sqrt (a:ℝ)) ≤ 2^(L+1) := by
    rw [pow_succ]
    linarith [Real.sqrt_nonneg (a:ℝ)]
  have hm := mul_le_mul_of_nonneg_right hinitial (show 0 ≤ (1/2:ℝ)^(L+p+3) by positivity)
  have he : (2:ℝ)^(L+1)*(1/2:ℝ)^(L+p+3)+2*((2:ℝ)^(p+2))⁻¹ =
      3/(4*(2:ℝ)^p) := by
    simp only [pow_add,div_pow,one_pow]
    field_simp
    <;> ring
  have hlast : 3/(4*(2:ℝ)^p) ≤ ((2:ℝ)^p)⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith [show 0 ≤ (2:ℝ)^p by positivity]
  calc
    _ ≤ (2:ℝ)^(L+1)*(1/2:ℝ)^(L+p+3)+2*((2:ℝ)^(p+2))⁻¹ := add_le_add_right hm _
    _ = _ := he
    _ ≤ _ := hlast

theorem certifiedSqrt_denominator (a : ℚ) (L p : ℕ) :
    ∃ z : ℤ, certifiedSqrt a L p=(z:ℚ)/(2:ℚ)^(p+2) := by
  exact rationalNewton_encoding (p+2) (L+p+2) a ((2:ℚ)^L+1)

/-- An explicit numerator bound, in addition to the common denominator.
Thus the output encoding needs O(L+p) bits, independently of iteration history. -/
theorem certifiedSqrt_encoding_bound (a : ℚ) (L p : ℕ) (ha : 0 < (a:ℝ))
    (hmag : (a:ℝ) ≤ (2:ℝ)^L) :
    ∃ z : ℤ,0 ≤ z ∧ z ≤ (2:ℤ)^(L+p+4) ∧
      certifiedSqrt a L p=(z:ℚ)/(2:ℚ)^(p+2) := by
  obtain ⟨z,hz⟩ := certifiedSqrt_denominator a L p
  have he := certifiedSqrt_error a L p ha hmag
  have htwo : (1:ℝ) ≤ 2^L := one_le_pow₀ (by norm_num)
  have heps : ((2:ℝ)^p)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hs : Real.sqrt (a:ℝ) ≤ (2:ℝ)^L+1 := by
    nlinarith [Real.sq_sqrt ha.le,Real.sqrt_nonneg (a:ℝ),sq_nonneg ((2:ℝ)^L)]
  have hupper : (certifiedSqrt a L p:ℝ) ≤ 4*(2:ℝ)^L := by linarith [he.2]
  have hzreal : (certifiedSqrt a L p:ℝ)=(z:ℝ)/(2:ℝ)^(p+2) := by exact_mod_cast hz
  have hmul : (z:ℝ)=(certifiedSqrt a L p:ℝ)*(2:ℝ)^(p+2) := by rw [hzreal]; field_simp
  have hz0 : (0:ℝ) ≤ z := by rw [hmul]; exact mul_nonneg ((Real.sqrt_nonneg _).trans he.1) (by positivity)
  have hzb : (z:ℝ) ≤ (2:ℝ)^(L+p+4) := by
    rw [hmul]
    calc
      _ ≤ (4*(2:ℝ)^L)*(2:ℝ)^(p+2) := mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = _ := by simp only [pow_add]; ring
  refine ⟨z,?_,?_,hz⟩
  · exact_mod_cast hz0
  · exact_mod_cast hzb

end Paper254
#print axioms Paper254.certifiedSqrt_error
#print axioms Paper254.certifiedSqrt_denominator
#print axioms Paper254.certifiedSqrt_encoding_bound
