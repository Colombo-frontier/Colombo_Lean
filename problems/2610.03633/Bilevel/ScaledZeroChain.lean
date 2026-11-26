import Bilevel.ZeroChainRegularity

/-! Exact rescaling of the manuscript's chain, including the active coordinate
and its dimension-dependent Euclidean gradient norm. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ScaledZeroChain
open ZeroChain

def value (n : ℕ) (a β : ℝ) (z : Space n) : ℝ :=
  a * ZeroChain.value n (β⁻¹ • z)

def gradientField (n : ℕ) (a β : ℝ) (z : Space n) : Space n :=
  (a / β) • gradient (ZeroChain.value n) (β⁻¹ • z)

theorem value_hasGradientAt (n : ℕ) (a β : ℝ) (z : Space n) :
    HasGradientAt (value n a β) (gradientField n a β z) z := by
  have hd := ((ZeroChain.value_hasGradientAt n (β⁻¹ • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul β⁻¹)).const_mul a
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd using 1
  ext v
  simp [gradientField, InnerProductSpace.toDual_apply, div_eq_mul_inv, ZeroChain.actual_gradient]
  ring

theorem actual_gradient (n : ℕ) (a β : ℝ) (z : Space n) :
    gradient (value n a β) z = gradientField n a β z :=
  (value_hasGradientAt n a β z).gradient

theorem value_contDiff (n k : ℕ) (a β : ℝ) : ContDiff ℝ k (value n a β) :=
  contDiff_const.mul ((ZeroChain.value_contDiff n k).comp (contDiff_id.const_smul β⁻¹))

theorem coordinate_norm_bound (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (v : Space n)
    (hv : ∀ j, |v j| ≤ B) : ‖v‖ ≤ B * Real.sqrt (n + 1 : ℕ) := by
  have hs : ‖v‖ ^ 2 ≤ (n + 1 : ℕ) * B ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _j : Fin (n + 1), B ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hv j) 2
      _ = _ := by simp
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).mp
  nlinarith

theorem gradient_norm_bound (n : ℕ) (a β B : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (hB : 0 ≤ B) (hbound : ∀ (z : Space n) j, |gradient (ZeroChain.value n) z j| ≤ B)
    (z : Space n) : ‖gradient (value n a β) z‖ ≤ a / β * B * Real.sqrt (n + 1 : ℕ) := by
  rw [actual_gradient, gradientField, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ha hβ.le)]
  exact (mul_le_mul_of_nonneg_left (coordinate_norm_bound n B hB _ (hbound _))
    (div_nonneg ha hβ.le)).trans_eq (by ring)

theorem frontier (n : ℕ) (a β : ℝ) (ha : 0 ≤ a) (hβ : 0 < β) (z : Space n)
    (hlast : |z (Fin.last n)| < β) :
    ∃ j : Fin (n + 1), |z j| < β ∧ gradient (value n a β) z j ≤ -(a / β) := by
  classical
  let s := Finset.univ.filter (fun j : Fin (n + 1) => |z j| < β)
  have hs : s.Nonempty := ⟨Fin.last n, by simp [s, hlast]⟩
  let j := s.min' hs
  have hj : |z j| < β := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hsmall : |(β⁻¹ • z) j| < 1 := by
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hβ)]
    exact (inv_mul_lt_iff₀ hβ).mpr (by simpa using hj)
  have hprevious : ∀ i : Fin (n + 1), i.val < j.val → 1 ≤ |(β⁻¹ • z) i| := by
    intro i hi
    have hzi : β ≤ |z i| := by
      by_contra hn
      have himem : i ∈ s := by simp [s, lt_of_not_ge hn]
      exact (not_lt_of_ge (Finset.min'_le s i himem)) hi
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hβ)]
    exact (le_inv_mul_iff₀ hβ).mpr (by simpa using hzi)
  have hgrad := ZeroChain.coordinate_endgame n (β⁻¹ • z) j hsmall hprevious
  refine ⟨j, hj, ?_⟩
  rw [actual_gradient, gradientField, PiLp.smul_apply, smul_eq_mul]
  simpa using mul_le_mul_of_nonneg_left hgrad (div_nonneg ha hβ.le)

theorem initial_gap_bound (n : ℕ) (a β : ℝ) (ha : 0 ≤ a) (z : Space n) :
    value n a β 0 - value n a β z ≤
      a * ((1 + 2 * Real.exp 1) * phiBound * (n + 1 : ℕ)) := by
  have h := mul_le_mul_of_nonneg_left (ZeroChain.initial_gap_bound n (β⁻¹ • z)) ha
  simpa [value, mul_sub] using h

end Bilevel.ScaledZeroChain
