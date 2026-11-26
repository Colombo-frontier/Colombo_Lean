import NCConcave16991.PersistentUpper
import NCConcave16991.AcceleratedUpper

/-! # The complete two upper bounds in Theorem 3.2 -/

namespace NCConcave16991

noncomputable section

/-- Both uniform randomized oracle algorithms exist with one explicit
universal constant. No algorithm-existence or convergence premise remains. -/
theorem theorem32_two_upper_bounds : Theorem32Specification := by
  refine ⟨(2 : ℝ) ^ 88, by positivity, ?_⟩
  intro p
  refine ⟨persistent_averaging_upper p, ?_⟩
  obtain ⟨budget, hb, hbound⟩ := accelerated_upper p
  refine ⟨budget, hb, hbound.trans ?_⟩
  have hA : 0 ≤ 1 + dimensionlessA p := by linarith [dimensionlessA_pos p]
  have hR : 0 ≤ (p.n : ℝ) + (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p :=
    add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (dimensionlessB_nonneg p))
  have hlog : 0 ≤ complexityLog p := le_trans (by norm_num) (Accelerated.complexityLog_one_le_public p)
  have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ 48 ≤ 2 ^ 88 by norm_num)
    (mul_nonneg (mul_nonneg hA hR) hlog)
  convert hh using 1 <;> ring

end

end NCConcave16991
