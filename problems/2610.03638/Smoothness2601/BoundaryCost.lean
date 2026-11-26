import Smoothness2601.BoundarySolve
import Smoothness2601.OuterSchedule

/-! Deterministic original-call budget for the boundary two-batch routine. -/
noncomputable section
namespace Smoothness2601.BoundaryCost
open BoundarySolve HypergradientKernels OuterSchedule

def batchConstant (b : Budgets) : ℝ := 2+1024*b.σ ^ 2*(1+innerScale b ^ 2)
def constant (b : Budgets) : ℝ := countConstant b*batchConstant b
def count (b : Budgets) (ε : ℝ) : ℕ := iterations b ε*BoundarySolve.count b ε

theorem batchConstant_pos (b : Budgets) : 0 < batchConstant b := by
  unfold batchConstant
  positivity

theorem constant_pos (b : Budgets) : 0 < constant b :=
  mul_pos (countConstant_pos b) (batchConstant_pos b)

theorem batch_upper (b : Budgets) {a : ℝ} (ha : 0 < a) :
    (outputBatch b 0 a:ℝ) ≤ 1+1024*b.σ ^ 2/a ^ 2 := by
  have hn : 0 ≤ 1024*b.σ ^ 2/a ^ 2 := by positivity
  unfold outputBatch
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,mul_one,Nat.cast_max,Nat.cast_one]
  exact max_le (by linarith) (by linarith [Nat.ceil_lt_add_one hn])

theorem per_outer (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (BoundarySolve.count b ε:ℝ) ≤ batchConstant b*(1/ε ^ 2) := by
  have hs := innerScale_pos b
  have hi := batch_upper b (div_pos hε hs)
  have hu := batch_upper b hε
  have hn : 1 ≤ 1/ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  change (innerCount b ε:ℝ) ≤ _ at hi
  change (upperCount b ε:ℝ) ≤ _ at hu
  have he : 1024*b.σ ^ 2/(ε/innerScale b) ^ 2 =
      1024*b.σ ^ 2*innerScale b ^ 2*(1/ε ^ 2) := by field_simp
  rw [he] at hi
  simp only [BoundarySolve.count,Nat.cast_add]
  unfold batchConstant
  calc
    _ ≤ (1+1024*b.σ ^ 2*innerScale b ^ 2*(1/ε ^ 2))+(1+1024*b.σ ^ 2/ε ^ 2) := add_le_add hi hu
    _ = 2+1024*b.σ ^ 2*(1+innerScale b ^ 2)*(1/ε ^ 2) := by ring
    _ ≤ 2*(1/ε ^ 2)+1024*b.σ ^ 2*(1+innerScale b ^ 2)*(1/ε ^ 2) :=
      add_le_add_right (by nlinarith [hn]) _
    _ = _ := by ring

theorem total (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (count b ε:ℝ) ≤ constant b*ε ^ (-4:ℝ) := by
  have hK := iterations_power_bound b hε hε1
  have hB := per_outer b hε hε1
  have hC := batchConstant_pos b
  have hb := mul_le_mul hK hB (Nat.cast_nonneg _) (by have := countConstant_pos b; positivity)
  have he : (1/ε ^ 2)*(1/ε ^ 2) = ε ^ (-4:ℝ) := by
    rw [Real.rpow_neg hε.le,show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast]
    field_simp
    ring
  calc
    _ = (iterations b ε:ℝ)*(BoundarySolve.count b ε:ℝ) := by simp only [count,Nat.cast_mul]
    _ ≤ _ := hb
    _ = (countConstant b*batchConstant b)*((1/ε ^ 2)*(1/ε ^ 2)) := by ring
    _ = _ := by rw [he]; rfl

end Smoothness2601.BoundaryCost
