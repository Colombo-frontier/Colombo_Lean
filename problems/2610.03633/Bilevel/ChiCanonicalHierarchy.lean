import Bilevel.ChiHierarchyCanonical
import Bilevel.ChiHierarchyHaar
import Bilevel.PrefixFrameStore

/-! One totalization for both hidden frames and retained prefixes. All-list
inverse certificates reduce to finitely many legal random nodes. Disclosed
data outside the finite depth is zero with retained count zero. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyIndex
open ChiTreeProgress ChiPrefixEvaluation

def retained (counts : ℕ → ℕ) (J q : ℕ) : FrameIndex counts J → ℕ
  | Sum.inl _ => counter counts (J+1) q 0 []
  | Sum.inr i => innerCounter counts J q i.1.val (nodeList i)

theorem retained_zero (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J) : retained counts J 0 i = 0 := by
  cases i with
  | inl _ => simp [retained,counter,nodePrefix,parentPrefix,nodeBudget]
  | inr i => exact FramePrefixDisclosure.inner_zero counts J _ _

theorem retained_le (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J) :
    retained counts J q i ≤ chainSize i+1 := by
  cases i with
  | inl _ =>
    change counter counts (J+1) q 0 [] ≤ counts 0+1
    rw [counter_at counts (J+1) q 0 [] rfl]
    exact nodePrefix_le _ _ _ _
  | inr i => exact FramePrefixDisclosure.inner_le counts J q _ _

theorem retained_success_bounds (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J) :
    retained counts J q i ≤ retained counts J (q+1) i ∧
      retained counts J (q+1) i ≤ retained counts J q i+1 := by
  cases i with
  | inl _ => exact counter_success_bounds counts (J+1) q 0 []
  | inr i => exact inner_counter_success_bounds counts J q _ _

def canonicalCounter (counts : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) : ℕ :=
  if hj : j ≤ J then retained counts J q (Sum.inr (canonicalNode counts J ⟨j,by omega⟩ I)) else 0

theorem canonicalCounter_at_node (counts : ℕ → ℕ) (J q : ℕ) (i : Node counts J) :
    canonicalCounter counts J q i.1.val (nodeList i) = innerCounter counts J q i.1.val (nodeList i) := by
  rw [canonicalCounter,dif_pos (Nat.le_of_lt_succ i.1.isLt)]
  change retained counts J q (Sum.inr (canonicalNode counts J i.1 (nodeList i))) = _
  rw [canonicalNode_at_node]
  rfl

theorem canonicalCounter_future (counts : ℕ → ℕ) (J q j : ℕ) (hj : j < J) (I : List ℕ)
    (i : Fin (counts (j+1)+1)) (hi : canonicalCounter counts J q j I ≤ i.val) :
    canonicalCounter counts J q (j+1) (I ++ [i.val]) ≤ counts ((j+1)+1) := by
  simp only [canonicalCounter,dif_pos hj.le,dif_pos (Nat.succ_le_of_lt hj),retained,
    canonicalNode,nodeList] at hi ⊢
  change innerCounter counts J q (j+1) (canonicalList counts ((j+1)+1) (I ++ [i.val])) ≤ _
  rw [canonicalList_append]
  exact counter_future counts (J+1) q (j+1) (canonicalList counts (j+1) I) (by omega) i hi

abbrev FiniteColumns (counts : ℕ → ℕ) (J : ℕ) (E : Type*) :=
  ∀ i : FrameIndex counts J, Fin (chainSize i+1) → E

def extendColumns {E : Type*} [Zero E] {counts : ℕ → ℕ} {J : ℕ}
    (C : FiniteColumns counts J E) (j : ℕ) (I : List ℕ) : Fin (counts (j+1)+1) → E :=
  if hj : j ≤ J then C (Sum.inr (canonicalNode counts J ⟨j,by omega⟩ I)) else 0

theorem extendColumns_at_node {E : Type*} [Zero E] {counts : ℕ → ℕ} {J : ℕ}
    (C : FiniteColumns counts J E) (i : Node counts J) :
    extendColumns C i.1.val (nodeList i) = C (Sum.inr i) := by
  rw [extendColumns,dif_pos (Nat.le_of_lt_succ i.1.isLt)]
  change C (Sum.inr ⟨i.1,canonicalPath counts (i.1.val+1) (toList i.2)⟩) = _
  rw [canonicalPath_toList]

theorem extendColumns_measurable {E : Type*} [Zero E] [MeasurableSpace E]
    (counts : ℕ → ℕ) (J : ℕ) : Measurable (extendColumns (E:=E) (counts:=counts) (J:=J)) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro I
  unfold extendColumns
  split_ifs with hj
  · exact measurable_pi_apply _
  · exact measurable_const

theorem extendColumns_continuous {E : Type*} [Zero E] [TopologicalSpace E]
    (counts : ℕ → ℕ) (J : ℕ) : Continuous (extendColumns (E:=E) (counts:=counts) (J:=J)) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro I
  unfold extendColumns
  split_ifs with hj
  · exact continuous_apply _
  · exact continuous_const

theorem extendColumns_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {counts : ℕ → ℕ} {J : ℕ} (C : FiniteColumns counts J E) (q : ℕ)
    (hC : ∀ i, PrefixGram (chainSize i) (retained counts J q i) (C i)) (j : ℕ) (I : List ℕ) :
    PrefixGram (counts (j+1)) (canonicalCounter counts J q j I) (extendColumns C j I) := by
  unfold canonicalCounter extendColumns
  split_ifs with hj
  · exact hC (Sum.inr (canonicalNode counts J ⟨j,by omega⟩ I))
  · intro i k hi
    omega

end Bilevel.ChiHierarchyIndex
