import Bilevel.WrappedChain

/-! Explicit universal choices for the two radial-wrapper margins. -/
noncomputable section
namespace Bilevel.WrappedChain
open ZeroChain

theorem wrapper_inner_margin (a β B t : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hB : 0 ≤ B) (ht : 0 < t) :
    (a / (24 * β ^ 2) + (a / β * B * t) / (48 * (B + 1) * β * t)) * β ≤
      (a / β) / 6 := by
  have hb : 0 < B + 1 := by linarith
  have hratio : B / (B + 1) ≤ 1 := (div_le_one hb).mpr (by linarith)
  have he : (a / (24 * β ^ 2) + (a / β * B * t) / (48 * (B + 1) * β * t)) * β =
      (a / β) / 24 + (a / β) / 48 * (B / (B + 1)) := by
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (a / β) / 48 by positivity)
  have hs := div_pos ha hβ
  nlinarith

theorem wrapper_outer_margin (a β B t : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hB : 0 ≤ B) (ht : 1 ≤ t) :
    (a / β) / 2 ≤ 2 * (a / (24 * β ^ 2)) * (48 * (B + 1) * β * t) / 3 -
      a / β * B * t := by
  have he : 2 * (a / (24 * β ^ 2)) * (48 * (B + 1) * β * t) / 3 - a / β * B * t =
      (a / β) * t * (B / 3 + 4 / 3) := by
    field_simp
    ring
  rw [he]
  have hs : 0 < a / β := div_pos ha hβ
  have hst : a / β ≤ (a / β) * t := by nlinarith
  have hb := mul_nonneg (mul_nonneg hs.le (by linarith : 0 ≤ t)) hB
  nlinarith

theorem sqrt_dimension_one_le (n : ℕ) : 1 ≤ Real.sqrt (n + 1 : ℕ) := by
  apply Real.one_le_sqrt.mpr
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `eta0 = 1/24` and `K = 48(B+1)` suffice, uniformly in the dimension. -/
theorem explicit_endgame (n : ℕ) (a β B : ℝ) (ha : 0 < a) (hβ : 0 < β) (hB : 0 ≤ B)
    (hbound : ∀ (z : Space n) j, |gradient (ZeroChain.value n) z j| ≤ B)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hlast : |coordinates n (48 * (B + 1) * β * Real.sqrt (n + 1 : ℕ)) U u (Fin.last n)| < β) :
    (a / β) / 2 ≤ ‖gradient
      (value n a β (a / (24 * β ^ 2)) (48 * (B + 1) * β * Real.sqrt (n + 1 : ℕ)) U) u‖ := by
  have ht := sqrt_dimension_one_le n
  have htp : 0 < Real.sqrt (n + 1 : ℕ) := lt_of_lt_of_le zero_lt_one ht
  have hb : 0 < B + 1 := by linarith
  exact endgame n a β (a / (24 * β ^ 2)) (48 * (B + 1) * β * Real.sqrt (n + 1 : ℕ)) B
    ha hβ (by positivity) (by positivity) hB hbound
    (wrapper_inner_margin a β B _ ha hβ hB htp) (wrapper_outer_margin a β B _ ha hβ hB ht) U u hlast

end Bilevel.WrappedChain
