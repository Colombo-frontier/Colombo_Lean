import SecondOrder.BinaryGeometry

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

def levelSpan (n l : ℕ) : Finset ℕ := Finset.Ico (binaryCut n (l+1)) (binaryCut n l)

theorem levelSpan_of_active {L : ℕ} (n : ℕ) (l : Fin L) (ha : binaryActive n l.val) :
    levelSpan n l.val = Finset.Ico (nodeLeft (activeNode n l)) (nodeRight (activeNode n l)) := by
  rw [(activeNode_endpoints n l ha).1, (activeNode_endpoints n l ha).2]
  rfl

theorem levelSpan_of_inactive (n l : ℕ) (ha : ¬ binaryActive n l) : levelSpan n l = ∅ := by
  simp [levelSpan, inactive_cuts_equal n l ha]

theorem binary_spans_cover (n L : ℕ) :
    (Finset.range L).biUnion (levelSpan n) = Finset.Ico (binaryCut n L) n := by
  induction L with
  | zero => simp [binaryCut_zero]
  | succ L ih =>
    rw [Finset.range_succ, Finset.biUnion_insert, ih]
    ext k
    have hs := binaryCut_mono_level n L
    have ht := binaryCut_le n L
    simp only [levelSpan, Finset.mem_union, Finset.mem_Ico]
    omega

theorem binary_partition_covers_prefix {n L : ℕ} (hn : n < 2^L) :
    (Finset.range L).biUnion (levelSpan n) = Finset.range n := by
  rw [binary_spans_cover, binaryCut_top hn]
  simp

theorem binary_spans_disjoint (n : ℕ) {l k : ℕ} (hlk : l ≠ k) :
    Disjoint (levelSpan n l) (levelSpan n k) := by
  have ha : Antitone (binaryCut n) := antitone_nat_of_succ_le (binaryCut_mono_level n)
  apply Finset.disjoint_left.mpr
  intro t ht hk
  have ht' := Finset.mem_Ico.mp ht
  have hk' := Finset.mem_Ico.mp hk
  rcases lt_or_gt_of_ne hlk with h|h
  · have hh := ha (show l+1 ≤ k by omega)
    omega
  · have hh := ha (show k+1 ≤ l by omega)
    omega

def completedNodes (L n : ℕ) : Finset (BinaryNode L) :=
  Finset.univ.biUnion (fun l : Fin L => (Finset.range (n/2^l.val)).image (fun j => (l,j)))

theorem mem_completedNodes {L n : ℕ} (i : BinaryNode L) :
    i ∈ completedNodes L n ↔ nodeRight i ≤ n := by
  have hp : 0 < 2^i.1.val := by positivity
  have he : i ∈ completedNodes L n ↔ i.2 < n/2^i.1.val := by
    rcases i with ⟨l,j⟩
    simp [completedNodes]
  rw [he, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hp]
  rfl

theorem completedNodes_mono (L : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    completedNodes L m ⊆ completedNodes L n := by
  intro i hi
  exact (mem_completedNodes i).mpr (((mem_completedNodes i).mp hi).trans hmn)

theorem completedNodes_zero (L : ℕ) : completedNodes L 0 = ∅ := by
  ext i
  simp only [mem_completedNodes, Finset.not_mem_empty, iff_false]
  exact Nat.not_le_of_lt (nodeRight_pos i)

theorem completedNodes_card (L n : ℕ) : (completedNodes L n).card ≤ 2*n := by
  calc
    _ ≤ ∑ l : Fin L, ((Finset.range (n/2^l.val)).image (fun j => (l,j))).card := Finset.card_biUnion_le
    _ ≤ ∑ l : Fin L, n/2^l.val := Finset.sum_le_sum (fun l _ =>
      Finset.card_image_le.trans_eq (Finset.card_range _))
    _ = ∑ l ∈ Finset.range L, n/2^l := Fin.sum_univ_eq_sum_range (fun l : ℕ => n/2^l) L
    _ ≤ 2*n := binary_node_count n L

/-- Exactly the finite query packet requested just after physical move t+1. -/
def createdNodes (L t : ℕ) : Finset (BinaryNode L) := completedNodes L (t+1) \ completedNodes L t

theorem mem_createdNodes {L t : ℕ} (i : BinaryNode L) :
    i ∈ createdNodes L t ↔ nodeRight i = t+1 := by
  simp only [createdNodes, Finset.mem_sdiff, mem_completedNodes]
  omega

theorem createdNodes_disjoint {L s t : ℕ} (hst : s ≠ t) :
    Disjoint (createdNodes L s) (createdNodes L t) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hh := (mem_createdNodes i).mp hi
  have hk := (mem_createdNodes i).mp hj
  omega

theorem all_created_nodes (L n : ℕ) :
    (Finset.range n).biUnion (createdNodes L) = completedNodes L n := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_createdNodes, mem_completedNodes]
  have hp := nodeRight_pos i
  constructor
  · rintro ⟨t,ht,he⟩
    omega
  · intro hi
    exact ⟨nodeRight i-1,by omega,by omega⟩

/-- Every physical move is charged once for each genuinely new direct chord.
This is a bound on the actual schedule, not only on a potential tree. -/
theorem total_created_nodes (L n : ℕ) :
    (∑ t ∈ Finset.range n, (createdNodes L t).card) ≤ 2*n := by
  have he : (∑ t ∈ Finset.range n, (createdNodes L t).card) = (completedNodes L n).card := by
    induction n with
    | zero => simp [completedNodes_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact (add_comm _ _).trans (Finset.card_sdiff_add_card_eq_card
        (completedNodes_mono L (Nat.le_succ n)))
  rw [he]
  exact completedNodes_card L n

end
end SecondOrder
