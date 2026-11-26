import SecondOrder.BinaryNodes

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

def activeNodes (L n : ℕ) : Finset (BinaryNode L) :=
  (Finset.univ.filter (fun l : Fin L => binaryActive n l.val)).image (activeNode n)

theorem activeNodes_card (L n : ℕ) : (activeNodes L n).card ≤ L :=
  Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (by simp))

theorem activeNodes_completed (L n : ℕ) : activeNodes L n ⊆ completedNodes L n := by
  intro i hi
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hi
  have ha := (Finset.mem_filter.mp hl).2
  apply (mem_completedNodes _).mpr
  rw [(activeNode_endpoints n l ha).2]
  exact binaryCut_le n l.val

/-- Persistent chord storage. At step t+1, only the newly completed nodes
receive freshly sampled direct chords. -/
def binaryTable {E : Type*} {L : ℕ} (packet : ℕ → BinaryNode L → E) :
    ℕ → BinaryNode L → Option E
  | 0, _ => none
  | t+1, i => if i ∈ createdNodes L t then some (packet t i) else binaryTable packet t i

theorem binaryTable_formula {E : Type*} {L : ℕ} (packet : ℕ → BinaryNode L → E)
    (n : ℕ) (i : BinaryNode L) :
    binaryTable packet n i = if nodeRight i ≤ n then some (packet (nodeRight i-1) i) else none := by
  have hp := nodeRight_pos i
  induction n with
  | zero => simp [binaryTable, Nat.not_le_of_lt hp]
  | succ n ih =>
    by_cases hc : nodeRight i = n+1
    · simp [binaryTable, mem_createdNodes, hc]
    · have he : nodeRight i ≤ n+1 ↔ nodeRight i ≤ n := by omega
      simp only [binaryTable, mem_createdNodes, hc, if_false, ih, he]

theorem binaryTable_stored {E : Type*} {L n : ℕ} (packet : ℕ → BinaryNode L → E)
    (i : BinaryNode L) (hi : i ∈ completedNodes L n) :
    binaryTable packet n i = some (packet (nodeRight i-1) i) := by
  rw [binaryTable_formula, if_pos ((mem_completedNodes i).mp hi)]

theorem binaryTable_future {E : Type*} {L n : ℕ} (packet : ℕ → BinaryNode L → E)
    (i : BinaryNode L) (hi : n < nodeRight i) : binaryTable packet n i = none := by
  rw [binaryTable_formula, if_neg (Nat.not_le_of_lt hi)]

def levelEstimate {E : Type*} [Zero E] {L : ℕ} (packet : ℕ → BinaryNode L → E)
    (n : ℕ) (l : Fin L) : E :=
  if binaryActive n l.val then (binaryTable packet n (activeNode n l)).getD 0 else 0

def binaryTracker {E : Type*} [AddCommMonoid E] {L : ℕ}
    (anchor : E) (packet : ℕ → BinaryNode L → E) (n : ℕ) : E :=
  anchor+∑ l : Fin L, levelEstimate packet n l

theorem levelEstimate_active {E : Type*} [Zero E] {L : ℕ}
    (packet : ℕ → BinaryNode L → E) (n : ℕ) (l : Fin L) (ha : binaryActive n l.val) :
    levelEstimate packet n l = packet (nodeRight (activeNode n l)-1) (activeNode n l) := by
  have hm : activeNode n l ∈ completedNodes L n := by
    apply (mem_completedNodes _).mpr
    rw [(activeNode_endpoints n l ha).2]
    exact binaryCut_le n l.val
  simp only [levelEstimate, if_pos ha, binaryTable_stored packet _ hm, Option.getD_some]

/-- Accuracy of the actual table update and readout. No assumed partition or
assumed active-count bound remains in this statement. -/
theorem binaryTracker_error {E : Type*} [NormedAddCommGroup E] {L n : ℕ}
    (G : ℕ → E) (anchor : E) (packet : ℕ → BinaryNode L → E)
    (hn : n < 2^L) {e ρ : ℝ} (hρ : 0 ≤ ρ) (ha : ‖anchor-G 0‖ ≤ e)
    (hc : ∀ i ∈ completedNodes L n,
      ‖packet (nodeRight i-1) i-(G (nodeRight i)-G (nodeLeft i))‖ ≤ ρ) :
    ‖binaryTracker anchor packet n-G n‖ ≤ e+(L : ℝ)*ρ := by
  let exactChord (l : Fin L) := if binaryActive n l.val then
    G (nodeRight (activeNode n l))-G (nodeLeft (activeNode n l)) else 0
  have ht : (∑ l : Fin L, exactChord l) = G n-G 0 := binary_partition_telescopes G n L hn
  have he : binaryTracker anchor packet n-G n =
      (anchor-G 0)+∑ l : Fin L, (levelEstimate packet n l-exactChord l) := by
    rw [Finset.sum_sub_distrib, ht]
    dsimp [binaryTracker]
    abel
  have hl (l : Fin L) : ‖levelEstimate packet n l-exactChord l‖ ≤ ρ := by
    by_cases hb : binaryActive n l.val
    · rw [levelEstimate_active packet n l hb]
      have hm : activeNode n l ∈ completedNodes L n := by
        apply (mem_completedNodes _).mpr
        rw [(activeNode_endpoints n l hb).2]
        exact binaryCut_le n l.val
      simpa only [exactChord, if_pos hb] using hc _ hm
    · simpa only [levelEstimate, exactChord, if_neg hb, sub_zero, norm_zero] using hρ
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add ha
  apply (norm_sum_le _ _).trans
  have hh := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hl l)
  simpa using hh

theorem binaryTracker_accuracy {E : Type*} [NormedAddCommGroup E] {L n : ℕ}
    (G : ℕ → E) (anchor : E) (packet : ℕ → BinaryNode L → E)
    (hn : n < 2^L) {τ ρ : ℝ} (hρ : 0 ≤ ρ) (ha : ‖anchor-G 0‖ ≤ τ/4)
    (hc : ∀ i ∈ completedNodes L n,
      ‖packet (nodeRight i-1) i-(G (nodeRight i)-G (nodeLeft i))‖ ≤ ρ)
    (hb : (L : ℝ)*ρ ≤ τ/4) : ‖binaryTracker anchor packet n-G n‖ ≤ τ/2 := by
  have h := binaryTracker_error G anchor packet hn hρ ha hc
  linarith

/-- One simultaneous local-success event controls every visited time. -/
theorem binaryTracker_uniform_accuracy {E : Type*} [NormedAddCommGroup E] (M : ℕ)
    (G : ℕ → E) (anchor : E) (packet : ℕ → BinaryNode (binaryDepth M) → E)
    {τ ρ : ℝ} (hρ : 0 ≤ ρ) (ha : ‖anchor-G 0‖ ≤ τ/4)
    (hc : ∀ i ∈ completedNodes (binaryDepth M) M,
      ‖packet (nodeRight i-1) i-(G (nodeRight i)-G (nodeLeft i))‖ ≤ ρ)
    (hb : (binaryDepth M : ℝ)*ρ ≤ τ/4) :
    ∀ n ≤ M, ‖binaryTracker anchor packet n-G n‖ ≤ τ/2 := by
  intro n hn
  exact binaryTracker_accuracy G anchor packet (binaryDepth_sufficient hn) hρ ha
    (fun i hi => hc i (completedNodes_mono _ hn hi)) hb

end
end SecondOrder
