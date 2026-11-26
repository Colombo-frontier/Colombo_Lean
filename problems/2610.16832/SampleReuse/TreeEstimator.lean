import SecondOrder.BinaryTracker
import Mathlib.Algebra.Order.Floor.Ring

/-! Deterministic parts of the binary-ancestor estimator: actual stored
chords telescope, errors accumulate only along active ancestors, and each
shared-sample edge is charged at both endpoints. Concentration is separate. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

/-- Only intervals whose right endpoint has this level as its least set bit
are used by any binary-ancestor readout. All other dyadic nodes can be omitted. -/
def usefulNode {L : ℕ} (i : BinaryNode L) : Prop := i.2 % 2 = 0

theorem activeNode_useful {L : ℕ} (n : ℕ) (l : Fin L)
    (ha : binaryActive n l.val) : usefulNode (activeNode n l) := by
  unfold usefulNode activeNode binaryActive at *
  dsimp only
  omega

/-- Unused packets are irrelevant to the actual cache readout. -/
theorem tree_readout_congr_useful {E : Type*} [AddCommMonoid E] {L : ℕ}
    (anchor : E) (p q : ℕ → BinaryNode L → E)
    (he : ∀ t i, usefulNode i → p t i = q t i) (n : ℕ) :
    binaryTracker anchor p n = binaryTracker anchor q n := by
  unfold binaryTracker
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  by_cases ha : binaryActive n l.val
  · rw [levelEstimate_active p n l ha, levelEstimate_active q n l ha]
    exact he _ _ (activeNode_useful n l ha)
  · simp only [levelEstimate, ha, if_false]

theorem tree_estimate_error {E : Type*} [NormedAddCommGroup E]
    (M : ℕ) (A : ℕ → E) (anchor : E)
    (packet : ℕ → BinaryNode (binaryDepth M) → E)
    {η : ℝ} (hη : 0 ≤ η)
    (hroot : ‖anchor-A 0‖ ≤ η/(binaryDepth M + 1))
    (hedge : ∀ i ∈ completedNodes (binaryDepth M) M,
      ‖packet (nodeRight i-1) i-(A (nodeRight i)-A (nodeLeft i))‖ ≤
        η/(binaryDepth M + 1)) :
    ∀ n ≤ M, ‖binaryTracker anchor packet n-A n‖ ≤ η := by
  intro n hn
  have he := binaryTracker_error A anchor packet (binaryDepth_sufficient hn)
    (show 0 ≤ η/((binaryDepth M : ℝ)+1) by positivity)
    hroot (fun i hi => hedge i (completedNodes_mono _ hn hi))
  have hden : (binaryDepth M : ℝ)+1 ≠ 0 := by positivity
  have hid : η/((binaryDepth M : ℝ)+1) + (binaryDepth M : ℝ)*
      (η/((binaryDepth M : ℝ)+1)) = η := by field_simp; ring
  rwa [hid] at he

/-- Accuracy requires bounds only for the sparse ancestor edges actually
used in the paper. Exact values assigned to unused packets exist only inside
this proof; `tree_readout_congr_useful` removes them from the readout. -/
theorem tree_estimate_error_useful {E : Type*} [NormedAddCommGroup E]
    (M : ℕ) (A : ℕ → E) (anchor : E)
    (packet : ℕ → BinaryNode (binaryDepth M) → E)
    {η : ℝ} (hη : 0 ≤ η)
    (hroot : ‖anchor-A 0‖ ≤ η/(binaryDepth M + 1))
    (hedge : ∀ i ∈ completedNodes (binaryDepth M) M, usefulNode i →
      ‖packet (nodeRight i-1) i-(A (nodeRight i)-A (nodeLeft i))‖ ≤
        η/(binaryDepth M + 1)) :
    ∀ n ≤ M, ‖binaryTracker anchor packet n-A n‖ ≤ η := by
  let extended := fun t i => if usefulNode i then packet t i
    else A (nodeRight i)-A (nodeLeft i)
  have he (t) (i) (hi : usefulNode i) : packet t i = extended t i := by
    simp only [extended, if_pos hi]
  intro n hn
  rw [tree_readout_congr_useful anchor packet extended he n]
  apply tree_estimate_error M A anchor extended hη hroot _ n hn
  intro i hi
  by_cases hu : usefulNode i
  · simpa only [extended, if_pos hu] using hedge i hi hu
  · simp only [extended, if_neg hu, sub_self, norm_zero]
    positivity

def batchSize (scale weight : ℝ) : ℕ := max 1 ⌈scale*weight⌉₊

theorem batchSize_pos (scale weight : ℝ) : 1 ≤ batchSize scale weight :=
  le_max_left _ _

theorem batchSize_sufficient (scale weight : ℝ) :
    scale*weight ≤ (batchSize scale weight : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

theorem batchSize_upper {scale weight : ℝ} (hs : 0 ≤ scale) (hw : 0 ≤ weight) :
    (batchSize scale weight : ℝ) ≤ 1+scale*weight := by
  unfold batchSize
  rw [Nat.cast_max]
  apply max_le
  · push_cast
    linarith [mul_nonneg hs hw]
  · have h := (Nat.ceil_lt_add_one (mul_nonneg hs hw)).le
    linarith

/-- Both endpoints of every same-sample difference are charged. -/
def treeQueryCost {ι : Type*} (edges : Finset ι) (scale rootWeight : ℝ)
    (edgeWeight : ι → ℝ) : ℕ :=
  batchSize scale rootWeight + 2*∑ i ∈ edges, batchSize scale (edgeWeight i)

theorem treeQueryCost_upper {ι : Type*} (edges : Finset ι)
    {scale rootWeight : ℝ} (edgeWeight : ι → ℝ)
    (hs : 0 ≤ scale) (hr : 0 ≤ rootWeight)
    (he : ∀ i ∈ edges, 0 ≤ edgeWeight i) :
    (treeQueryCost edges scale rootWeight edgeWeight : ℝ) ≤
      1+2*(edges.card : ℝ)+scale*(rootWeight+2*∑ i ∈ edges, edgeWeight i) := by
  have hroot := batchSize_upper hs hr
  have hedge := Finset.sum_le_sum (fun i hi => batchSize_upper hs (he i hi))
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum] at hedge
  unfold treeQueryCost
  push_cast
  linarith

end
end SampleReuse
