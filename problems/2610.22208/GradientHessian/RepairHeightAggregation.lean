import GradientHessian.RepairAllocation
import GradientHessian.GeometricRepairInventory

/-! Finite aggregation of the actual heterogeneous reliability allocation.
The probability estimates for the stopped action events are separate inputs. -/

noncomputable section
namespace GradientHessian.RepairHeightAggregation
open Allocation AllocationParameters RepairAllocation
open scoped BigOperators

theorem allocated_height_sum {K : ℝ} (hK : 0<K) (Cp : ℝ) (M t : ℕ) :
    (∑ j ∈ Finset.range t,
      levelCost K (levelDimension (lowDimension Cp M) (cutoff M) (j+2)) j) ≤
      256*(6/K)^(lowDimension Cp M-1) + 256*(6/K)^7/(2+(M:ℝ))^4 := by
  have hc := cutoff_ge_two M
  by_cases ht : t≤cutoff M-2
  · have he : (∑ j ∈ Finset.range t,
        levelCost K (levelDimension (lowDimension Cp M) (cutoff M) (j+2)) j) =
        ∑ j ∈ Finset.range t, levelCost K (lowDimension Cp M) j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [levelDimension,if_pos (by omega)]
    rw [he]
    exact (low_dimension_cost_bound hK (lowDimension_ge_eight Cp M) t).trans
      (le_add_of_nonneg_right (by positivity))
  · have ht' : t=(cutoff M-2)+(t-(cutoff M-2)) := by omega
    conv_lhs => rw [ht',Finset.sum_range_add]
    have hlo : (∑ j ∈ Finset.range (cutoff M-2),
        levelCost K (levelDimension (lowDimension Cp M) (cutoff M) (j+2)) j) =
        ∑ j ∈ Finset.range (cutoff M-2), levelCost K (lowDimension Cp M) j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [levelDimension,if_pos (by omega)]
    have hhi : (∑ j ∈ Finset.range (t-(cutoff M-2)),
        levelCost K (levelDimension (lowDimension Cp M) (cutoff M)
          (cutoff M-2+j+2)) (cutoff M-2+j)) =
        ∑ j ∈ Finset.range (t-(cutoff M-2)),
          Reliability.fixedDimensionCost K (cutoff M-2+j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [levelDimension,if_neg (by omega)]
      exact Reliability.fixed_dimension_cost_eq K (cutoff M-2+j)
    rw [hlo,hhi]
    exact add_le_add
      (low_dimension_cost_bound hK (lowDimension_ge_eight Cp M) (cutoff M-2))
      (fixed_tail_bound hK M (t-(cutoff M-2)))

def localizedBound (K Cp : ℝ) (M ell : ℕ) (j : ℕ) : ℝ :=
  (M:ℝ)*ell*levelCost K (levelDimension (lowDimension Cp M) (cutoff M) (j+2)) j

def memoryDecay (Cp : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-(lowDimension Cp M:ℝ)/18432)

def oldBound (Cp : ℝ) (M ell : ℕ) : ℝ := 16*M*ell*memoryDecay Cp M
def innerBound (Cp : ℝ) (M ell : ℕ) : ℝ := 2*M*ell*memoryDecay Cp M
def markBound (M ell r : ℕ) : ℝ := 2*M*ell*Real.exp (-(r:ℝ)/75497472)

theorem localized_sum {K : ℝ} (hK : 0<K) (Cp : ℝ) (M ell t : ℕ) :
    (15/8:ℝ)*(∑ j : Fin t, localizedBound K Cp M ell j.val) ≤
      480*M*ell*(6/K)^(lowDimension Cp M-1) +
      480*M*ell*(6/K)^7/(2+(M:ℝ))^4 := by
  rw [Fin.sum_univ_eq_sum_range]
  simp only [localizedBound,← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (allocated_height_sum hK Cp M t)
    (show (0:ℝ)≤(15/8)*M*ell by positivity)
  convert h using 1 <;> ring

theorem normalized_family_bound {K Cp : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    {M ell r : ℕ} (hM : 1≤M) (hell : ell≤M)
    (hr : markAllocation*(M:ℝ)≤r) (t : ℕ) :
    (15/8:ℝ)*(∑ j : Fin t, localizedBound K Cp M ell j.val) +
      8*(FirstHeight.depth M+2)*oldBound Cp M ell +
      M*(Inner.absoluteDepth+2)*innerBound Cp M ell + M*markBound M ell r ≤ 1/256 := by
  have hl := localized_sum (K := K) (by linarith) Cp M ell t
  have hlow := low_contribution hK hCp hM hell
  have hhigh := high_contribution hK hM hell
  have hold := old_contribution hCp hM hell
  have hin := inner_contribution hCp hM hell
  have hm := mark_contribution hM hell hr
  norm_num [oldBound,innerBound,markBound,memoryDecay,Inner.absoluteDepth] at *
  nlinarith

theorem family_cost_bound {K Cp : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    {m ell r : ℕ} (hell : ell≤m+1)
    (hr : markAllocation*((m+1:ℕ):ℝ)≤r) (t : ℕ) :
    (∑ a : GeometricRepair.Action t m, (GeometricRepair.publicCost a:ℝ)*
      GeometricRepair.familyBound (fun h => localizedBound K Cp (m+1) ell h.val)
        (oldBound Cp (m+1) ell) (innerBound Cp (m+1) ell) (markBound (m+1) ell r) a) ≤
      (8:ℝ)^(t+1)*(m+1)/256 := by
  rw [GeometricRepair.family_cost_sum]
  have h := mul_le_mul_of_nonneg_left
    (normalized_family_bound hK hCp (by omega : 1≤m+1) hell hr t)
    (show (0:ℝ)≤8^(t+1)*(m+1) by positivity)
  simpa only [Nat.cast_add,Nat.cast_one,mul_one_div] using h

end GradientHessian.RepairHeightAggregation
