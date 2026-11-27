import FullMain

namespace Task006.Full
noncomputable section

/-- The closing common polynomial envelope, with the factor 2^(3/2)
absorbed into an absolute constant chosen before all public parameters. -/
theorem common_polynomial_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L R eps : ℝ), Regime d L R eps →
      (d : ℝ)*(L*R/eps)^3/131072 ≤ (minimaxReplies.{0,0} d L R eps : ℝ) ∧
      (minimaxReplies.{0,0} d L R eps : ℝ) ≤
        C*d*(L*R/eps)^3*Real.log (Real.exp 1+d+(L*R/eps))^(3/2:ℝ) := by
  obtain ⟨C,hC,hmain⟩ := main_theorem
  refine ⟨2^(3/2:ℝ)*C,by positivity,?_⟩
  intro d L R eps h
  obtain ⟨hd,hL,hR,heps,hreg⟩ := h
  have hA : 0 < L*R/eps := by positivity
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hA1 : 1 ≤ L*R/eps := by
    have := (le_max_right (d:ℝ) (2^17:ℝ)).trans hreg
    norm_num at this ⊢
    linarith
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hl0 : 0 ≤ Real.log (Real.exp 1*d*(L*R/eps)) := by
    apply Real.log_nonneg
    nlinarith [mul_le_mul hd1 hA1 (by norm_num : (0:ℝ) ≤ 1) hd0.le]
  have hs0 : 0 ≤ Real.log (Real.exp 1+d+(L*R/eps)) :=
    Real.log_nonneg (by linarith)
  obtain ⟨hl,hu⟩ := hmain d L R eps ⟨hd,hL,hR,heps,hreg⟩
  refine ⟨hl,hu.trans ?_⟩
  have hp := Real.rpow_le_rpow hl0
    (logarithm_product_le_twice_sum d (L*R/eps) hd0 hA) (by norm_num : (0:ℝ) ≤ 3/2)
  calc
    C*d*(L*R/eps)^3*Real.log (Real.exp 1*d*(L*R/eps))^(3/2:ℝ) ≤
        C*d*(L*R/eps)^3*(2*Real.log (Real.exp 1+d+(L*R/eps)))^(3/2:ℝ) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2^(3/2:ℝ)*C)*d*(L*R/eps)^3*
        Real.log (Real.exp 1+d+(L*R/eps))^(3/2:ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hs0]
      ring

/-- The regime includes A=d tending to infinity, where the polynomial
dependence is d^4, with the same absolute upper constant. -/
theorem diagonal_dimension_four :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L R eps : ℝ), Regime d L R eps →
      L*R/eps=(d:ℝ) →
      (d : ℝ)^4/131072 ≤ (minimaxReplies.{0,0} d L R eps : ℝ) ∧
      (minimaxReplies.{0,0} d L R eps : ℝ) ≤
        C*(d:ℝ)^4*Real.log (Real.exp 1*(d:ℝ)^2)^(3/2:ℝ) := by
  obtain ⟨C,hC,hmain⟩ := main_theorem
  refine ⟨C,hC,?_⟩
  intro d L R eps h hA
  obtain ⟨hl,hu⟩ := hmain d L R eps h
  rw [hA] at hl hu
  have hpoly : (d:ℝ)*(d:ℝ)^3=(d:ℝ)^4 := by ring
  have hlog : Real.exp 1*(d:ℝ)*(d:ℝ)=Real.exp 1*(d:ℝ)^2 := by ring
  constructor
  · simpa only [hpoly] using hl
  · simpa only [hlog,← mul_assoc,show C*(d:ℝ)*(d:ℝ)^3=C*(d:ℝ)^4 by ring] using hu

#print axioms common_polynomial_envelope
#print axioms diagonal_dimension_four
end
end Task006.Full
