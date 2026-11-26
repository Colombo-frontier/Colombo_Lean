import GradientHessian.FrontierState

/-!
# Concrete marked-task counters on the finite leaf tree

Each leaf has a completed prefix of its M tasks and an ordinary slot counter
for the current task. Retired leaves are derived from the completed prefix;
they are not an independent flag. Updates and charges below are deterministic
data operations. No oracle or probability statement is a field of the state.
-/

noncomputable section
namespace GradientHessian.TaskState

open FrontierState Classical
open scoped BigOperators

@[ext] structure State (L M ell : ℕ) where
  completed : Leaf L → Fin (M+1)
  slots : Leaf L → Fin (ell+1)

variable {L M ell : ℕ}

def initial : State L M ell := ⟨fun _ => 0,fun _ => 0⟩

def retired (s : State L M ell) : Retired L :=
  Finset.univ.filter (fun leaf => (s.completed leaf).val = M)

@[simp] theorem mem_retired (s : State L M ell) (leaf : Leaf L) :
    leaf ∈ retired s ↔ (s.completed leaf).val = M := by simp [retired]

def current (s : State L M ell) : Option (Leaf L) := FrontierState.current (retired s)

def remaining (s : State L M ell) (leaf : Leaf L) : ℕ := M-(s.completed leaf).val

def completedTotal (s : State L M ell) : ℕ := ∑ leaf,(s.completed leaf).val

def WellFormed (s : State L M ell) : Prop :=
  ∀ leaf, (s.completed leaf).val = M → (s.slots leaf).val = 0

theorem initial_wellFormed : WellFormed (initial : State L M ell) := by
  intro leaf _
  rfl

theorem current_live (s : State L M ell) {leaf : Leaf L} (h : current s = some leaf) :
    (s.completed leaf).val < M := by
  have hn := ((FrontierState.current_eq_some_iff (retired s) leaf).mp h).1
  have hb := (s.completed leaf).isLt
  rw [mem_retired] at hn
  omega

theorem completedTotal_le (s : State L M ell) : completedTotal s ≤ 8^L*M := by
  calc
    _ ≤ ∑ _leaf : Leaf L,M := Finset.sum_le_sum (fun leaf _ => by have := (s.completed leaf).isLt; omega)
    _ = 8^L*M := by simp [leaf_card]

theorem remaining_accounting (s : State L M ell) :
    (∑ leaf,remaining s leaf)+completedTotal s = 8^L*M := by
  rw [completedTotal,← Finset.sum_add_distrib]
  have he leaf : remaining s leaf+(s.completed leaf).val = M := by
    have := (s.completed leaf).isLt
    unfold remaining
    omega
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,leaf_card]
  norm_cast

def retireSet (s : State L M ell) (S : Finset (Leaf L)) : State L M ell where
  completed := fun leaf => if leaf ∈ S then Fin.last M else s.completed leaf
  slots := fun leaf => if leaf ∈ S then 0 else s.slots leaf

def retireNode (s : State L M ell) (v : Node L) : State L M ell := retireSet s (subtree v)

/-- Actual remaining tasks, so an already retired leaf contributes zero. -/
def charge (s : State L M ell) (S : Finset (Leaf L)) : ℕ :=
  ∑ leaf,if leaf ∈ S then remaining s leaf else 0

theorem charge_eq_sum (s : State L M ell) (S : Finset (Leaf L)) :
    charge s S = ∑ leaf ∈ S,remaining s leaf := by
  simp [charge,Finset.sum_ite_mem]

@[simp] theorem remaining_retireSet (s : State L M ell) (S : Finset (Leaf L)) (leaf : Leaf L) :
    remaining (retireSet s S) leaf = if leaf ∈ S then 0 else remaining s leaf := by
  by_cases hs : leaf ∈ S <;> simp [remaining,retireSet,hs]

theorem retired_retireSet (s : State L M ell) (S : Finset (Leaf L)) :
    retired (retireSet s S) = retired s ∪ S := by
  ext leaf
  by_cases hs : leaf ∈ S <;> simp [retireSet,hs]

theorem retireSet_wellFormed {s : State L M ell} (hs : WellFormed s) (S : Finset (Leaf L)) :
    WellFormed (retireSet s S) := by
  intro leaf hc
  by_cases hl : leaf ∈ S
  · simp [retireSet,hl]
  · simpa [retireSet,hl] using hs leaf (by simpa [retireSet,hl] using hc)

theorem retireSet_union (s : State L M ell) (S T : Finset (Leaf L)) :
    retireSet (retireSet s S) T = retireSet s (S ∪ T) := by
  apply State.ext <;> funext leaf <;>
    by_cases hs : leaf ∈ S <;> by_cases ht : leaf ∈ T <;> simp [retireSet,hs,ht]

theorem charge_retireSet_self (s : State L M ell) (S : Finset (Leaf L)) :
    charge (retireSet s S) S = 0 := by
  unfold charge
  apply Finset.sum_eq_zero
  intro leaf _
  by_cases hs : leaf ∈ S <;> simp [hs]

theorem charge_union (s : State L M ell) (S T : Finset (Leaf L)) :
    charge s (S ∪ T) = charge s S + charge (retireSet s S) T := by
  unfold charge
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf _
  by_cases hs : leaf ∈ S <;> by_cases ht : leaf ∈ T <;> simp [hs,ht]

theorem completedTotal_retireSet (s : State L M ell) (S : Finset (Leaf L)) :
    completedTotal (retireSet s S) = completedTotal s + charge s S := by
  unfold completedTotal charge
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf _
  have hb := (s.completed leaf).isLt
  by_cases hs : leaf ∈ S <;> simp [retireSet,remaining,hs]
  omega

theorem charge_zero_of_retired {s : State L M ell} {S : Finset (Leaf L)}
    (hS : S ⊆ retired s) : charge s S = 0 := by
  apply Finset.sum_eq_zero
  intro leaf _
  by_cases hs : leaf ∈ S
  · have he := (mem_retired s leaf).mp (hS hs)
    simp [hs,remaining,he]
  · simp [hs]

theorem charge_le (s : State L M ell) (S : Finset (Leaf L)) : charge s S ≤ S.card*M := by
  rw [charge_eq_sum]
  calc
    _ ≤ ∑ _leaf ∈ S,M := Finset.sum_le_sum (fun leaf _ => Nat.sub_le _ _)
    _ = S.card*M := by simp

theorem retireNode_retired (s : State L M ell) (v : Node L) :
    retired (retireNode s v) = FrontierState.retireSubtree (retired s) v :=
  retired_retireSet s (subtree v)

theorem retireNode_charge (s : State L M ell) (v : Node L) :
    completedTotal (retireNode s v) = completedTotal s + charge s (subtree v) :=
  completedTotal_retireSet s (subtree v)

theorem node_charge_le (s : State L M ell) (v : Node L) :
    charge s (subtree v) ≤ 8^(L-v.1.val)*M := by
  simpa only [subtree_card] using charge_le s (subtree v)

def completeLeaf (s : State L M ell) (leaf : Leaf L) : State L M ell :=
  if h : (s.completed leaf).val < M then
    ⟨Function.update s.completed leaf ⟨(s.completed leaf).val+1,by omega⟩,
      Function.update s.slots leaf 0⟩ else s

theorem completeLeaf_completed (s : State L M ell) (leaf : Leaf L)
    (hl : (s.completed leaf).val < M) :
    ((completeLeaf s leaf).completed leaf).val = (s.completed leaf).val+1 := by
  simp [completeLeaf,hl]

theorem completeLeaf_slots (s : State L M ell) (leaf : Leaf L)
    (hl : (s.completed leaf).val < M) : (completeLeaf s leaf).slots leaf = 0 := by
  simp [completeLeaf,hl]

theorem completeLeaf_other (s : State L M ell) (leaf other : Leaf L) (hne : other ≠ leaf) :
    (completeLeaf s leaf).completed other = s.completed other ∧
      (completeLeaf s leaf).slots other = s.slots other := by
  unfold completeLeaf
  split_ifs <;> simp [hne]

theorem completeLeaf_wellFormed {s : State L M ell} (hs : WellFormed s) (leaf : Leaf L) :
    WellFormed (completeLeaf s leaf) := by
  intro other hc
  by_cases ho : other = leaf
  · subst other
    by_cases hl : (s.completed leaf).val < M
    · rw [completeLeaf_slots s leaf hl]
      rfl
    · simpa [completeLeaf,hl] using hs leaf (by simpa [completeLeaf,hl] using hc)
  · rw [(completeLeaf_other s leaf other ho).2]
    exact hs other (by simpa only [(completeLeaf_other s leaf other ho).1] using hc)

theorem completedTotal_completeLeaf (s : State L M ell) (leaf : Leaf L)
    (hl : (s.completed leaf).val < M) :
    completedTotal (completeLeaf s leaf) = completedTotal s+1 := by
  have he other : ((completeLeaf s leaf).completed other).val =
      (s.completed other).val + if other = leaf then 1 else 0 := by
    by_cases h : other = leaf
    · subst other
      simp [completeLeaf_completed s leaf hl]
    · simp [(completeLeaf_other s leaf other h).1,h]
  simp only [completedTotal,he,Finset.sum_add_distrib]
  simp

theorem retired_completeLeaf (s : State L M ell) (leaf : Leaf L)
    (hl : (s.completed leaf).val < M) :
    retired (completeLeaf s leaf) =
      if (s.completed leaf).val+1 = M then insert leaf (retired s) else retired s := by
  ext other
  by_cases ho : other = leaf
  · subst other
    by_cases ht : (s.completed leaf).val+1 = M <;>
      simp [ht,mem_retired,completeLeaf_completed s leaf hl,show (s.completed leaf).val ≠ M by omega]
  · by_cases ht : (s.completed leaf).val+1 = M <;>
      simp [ht,mem_retired,(completeLeaf_other s leaf other ho).1,ho]

def normalComplete (s : State L M ell) : State L M ell :=
  match current s with | none => s | some leaf => completeLeaf s leaf

theorem normalComplete_gain (s : State L M ell) {leaf : Leaf L} (hc : current s = some leaf) :
    completedTotal (normalComplete s) = completedTotal s+1 := by
  simpa only [normalComplete,hc] using completedTotal_completeLeaf s leaf (current_live s hc)

theorem normalComplete_resets_slot (s : State L M ell) {leaf : Leaf L} (hc : current s = some leaf) :
    (normalComplete s).slots leaf = 0 := by
  simpa only [normalComplete,hc] using completeLeaf_slots s leaf (current_live s hc)

theorem normalComplete_wellFormed {s : State L M ell} (hs : WellFormed s) :
    WellFormed (normalComplete s) := by
  cases hc : current s with
  | none => simpa [normalComplete,hc] using hs
  | some leaf => simpa [normalComplete,hc] using completeLeaf_wellFormed hs leaf

theorem retired_subset_normalComplete (s : State L M ell) : retired s ⊆ retired (normalComplete s) := by
  cases hc : current s with
  | none => simp [normalComplete,hc]
  | some leaf =>
      simp only [normalComplete,hc,retired_completeLeaf s leaf (current_live s hc)]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _

def richComplete (s : State L M ell) : State L M ell :=
  match current s with | none => s | some leaf => retireSet s {leaf}

theorem richComplete_retired (s : State L M ell) {leaf : Leaf L} (hc : current s = some leaf) :
    retired (richComplete s) = insert leaf (retired s) := by
  simp only [richComplete,hc,retired_retireSet]
  ext other
  simp [or_comm]

theorem richComplete_charge (s : State L M ell) {leaf : Leaf L} (hc : current s = some leaf) :
    completedTotal (richComplete s) = completedTotal s + remaining s leaf := by
  simpa [richComplete,hc,charge_eq_sum] using completedTotal_retireSet s {leaf}

theorem richComplete_other (s : State L M ell) {leaf : Leaf L} (hc : current s = some leaf)
    (other : Leaf L) (hne : other ≠ leaf) :
    (richComplete s).completed other = s.completed other ∧
      (richComplete s).slots other = s.slots other := by simp [richComplete,hc,retireSet,hne]

theorem richComplete_wellFormed {s : State L M ell} (hs : WellFormed s) :
    WellFormed (richComplete s) := by
  cases hc : current s with
  | none => simpa [richComplete,hc] using hs
  | some leaf => simpa [richComplete,hc] using retireSet_wellFormed hs {leaf}

end GradientHessian.TaskState
