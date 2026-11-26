import Mathlib.Order.PiLex
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite tree retirement and a deterministic subtree repair loop

Leaves are length-L words over eight child indices, in lexicographic order.
Retirement is an arbitrary subset: an out-of-order subtree repair need not
produce a retired prefix. Repair actions below always retire an actual prefix
subtree. Their trigger is an input predicate, not an assumed oracle reply or
probability estimate. Instantiating those triggers with the manuscript's
geometric tests and proving disclosure invariants are separate tasks.
-/

noncomputable section
namespace GradientHessian.FrontierState

open Classical

abbrev Leaf (L : ℕ) := Lex (Fin L → Fin 8)
abbrev Node (L : ℕ) := (d : Fin (L+1)) × (Fin d.val → Fin 8)
abbrev Retired (L : ℕ) := Finset (Leaf L)

theorem leaf_card (L : ℕ) : Fintype.card (Leaf L) = 8^L := by
  simp [Leaf]

def InSubtree {L : ℕ} (v : Node L) (leaf : Leaf L) : Prop :=
  ∀ i : Fin v.1.val, leaf (i.castLE (Nat.le_of_lt_succ v.1.isLt)) = v.2 i

def subtree {L : ℕ} (v : Node L) : Finset (Leaf L) :=
  Finset.univ.filter (InSubtree v)

@[simp] theorem mem_subtree {L : ℕ} (v : Node L) (leaf : Leaf L) :
    leaf ∈ subtree v ↔ InSubtree v leaf := by simp [subtree]

def root (L : ℕ) : Node L := ⟨⟨0,by omega⟩,fun i => Fin.elim0 i⟩

def leafNode {L : ℕ} (leaf : Leaf L) : Node L := ⟨⟨L,by omega⟩,ofLex leaf⟩

@[simp] theorem subtree_root (L : ℕ) : subtree (root L) = Finset.univ := by
  ext leaf
  simp [InSubtree,root]

@[simp] theorem subtree_leafNode {L : ℕ} (leaf : Leaf L) :
    subtree (leafNode leaf) = {leaf} := by
  ext other
  simp only [mem_subtree,Finset.mem_singleton]
  change (∀ i : Fin L, other i = leaf i) ↔ other = leaf
  exact ⟨fun h => funext h,fun h => by subst other; simp⟩

def child {L : ℕ} (v : Node L) (h : v.1.val < L) (a : Fin 8) : Node L :=
  ⟨⟨v.1.val+1,by omega⟩,fun i => if hi : i.val < v.1.val then v.2 ⟨i.val,hi⟩ else a⟩

theorem inSubtree_child_iff {L : ℕ} (v : Node L) (h : v.1.val < L)
    (a : Fin 8) (leaf : Leaf L) :
    InSubtree (child v h a) leaf ↔ InSubtree v leaf ∧ leaf ⟨v.1.val,h⟩ = a := by
  change (∀ i : Fin (v.1.val+1), leaf (i.castLE (by omega)) =
    if hi : i.val < v.1.val then v.2 ⟨i.val,hi⟩ else a) ↔ _
  constructor
  · intro hc
    constructor
    · intro i
      have hh := hc ⟨i.val,by omega⟩
      simpa [i.isLt] using hh
    · have hh := hc ⟨v.1.val,by omega⟩
      simpa using hh
  · rintro ⟨hp,ha⟩ i
    by_cases hi : i.val < v.1.val
    · have hh := hp ⟨i.val,hi⟩
      simpa [hi] using hh
    · have he : i.val = v.1.val := by omega
      rw [dif_neg hi]
      have hindex : i.castLE (by omega : v.1.val+1 ≤ L) = (⟨v.1.val,h⟩ : Fin L) := Fin.ext he
      rw [hindex]
      exact ha

theorem subtree_child_subset {L : ℕ} (v : Node L) (h : v.1.val < L) (a : Fin 8) :
    subtree (child v h a) ⊆ subtree v := by
  intro leaf hl
  exact (mem_subtree v leaf).mpr ((inSubtree_child_iff v h a leaf).mp (mem_subtree _ _ |>.mp hl)).1

theorem subtree_children_disjoint {L : ℕ} (v : Node L) (h : v.1.val < L)
    {a b : Fin 8} (hab : a ≠ b) :
    Disjoint (subtree (child v h a)) (subtree (child v h b)) := by
  apply Finset.disjoint_left.mpr
  intro leaf ha hb
  have hea := ((inSubtree_child_iff v h a leaf).mp ((mem_subtree _ _).mp ha)).2
  have heb := ((inSubtree_child_iff v h b leaf).mp ((mem_subtree _ _).mp hb)).2
  exact hab (hea.symm.trans heb)

theorem subtree_eq_children {L : ℕ} (v : Node L) (h : v.1.val < L) :
    subtree v = Finset.univ.biUnion (fun a : Fin 8 => subtree (child v h a)) := by
  ext leaf
  simp only [mem_subtree,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · intro hp
    exact ⟨leaf ⟨v.1.val,h⟩,(inSubtree_child_iff v h _ leaf).mpr ⟨hp,rfl⟩⟩
  · rintro ⟨a,ha⟩
    exact ((inSubtree_child_iff v h a leaf).mp ha).1

theorem subtree_card {L : ℕ} (v : Node L) : (subtree v).card = 8^(L-v.1.val) := by
  by_cases he : v.1.val = L
  · rcases v with ⟨⟨d,hd⟩,word⟩
    simp only [Fin.val_mk] at he
    subst d
    change (subtree (leafNode (toLex word))).card = 8^(L-L)
    simp
  · have hd : v.1.val < L := by have := v.1.isLt; omega
    rw [subtree_eq_children v hd,Finset.card_biUnion]
    · have hc (a : Fin 8) := subtree_card (child v hd a)
      simp_rw [hc]
      simp only [child,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hn : L-v.1.val = (L-(v.1.val+1))+1 := by omega
      rw [hn,Nat.pow_succ,Nat.mul_comm]
      norm_num
    · intro a _ b _ hab
      exact subtree_children_disjoint v hd hab
termination_by L-v.1.val
decreasing_by simp only [child]; omega

def unretired {L : ℕ} (R : Retired L) : Finset (Leaf L) := Finset.univ \ R

@[simp] theorem mem_unretired {L : ℕ} (R : Retired L) (leaf : Leaf L) :
    leaf ∈ unretired R ↔ leaf ∉ R := by simp [unretired]

def current {L : ℕ} (R : Retired L) : Option (Leaf L) :=
  if h : (unretired R).Nonempty then some ((unretired R).min' h) else none

theorem current_eq_some_iff {L : ℕ} (R : Retired L) (leaf : Leaf L) :
    current R = some leaf ↔ leaf ∉ R ∧ ∀ other, other ∉ R → leaf ≤ other := by
  unfold current
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro he
      subst leaf
      exact ⟨(mem_unretired _ _).mp (Finset.min'_mem _ h),
        fun other ho => Finset.min'_le _ _ ((mem_unretired _ _).mpr ho)⟩
    · rintro ⟨hl,hmin⟩
      exact le_antisymm (Finset.min'_le _ _ ((mem_unretired _ _).mpr hl))
        (hmin _ ((mem_unretired _ _).mp (Finset.min'_mem _ h)))
  · simp only [Option.noConfusion, false_iff, not_and]
    intro hl
    exact False.elim (h ⟨leaf,(mem_unretired _ _).mpr hl⟩)

theorem current_none_iff {L : ℕ} (R : Retired L) : current R = none ↔ R = Finset.univ := by
  unfold current
  split_ifs with h
  · simp only [Option.noConfusion, false_iff]
    intro he
    subst R
    simp [unretired] at h
  · simp only [true_iff]
    apply Finset.eq_univ_iff_forall.mpr
    intro leaf
    by_contra hl
    exact h ⟨leaf,(mem_unretired _ _).mpr hl⟩

theorem current_mono {L : ℕ} {R S : Retired L} (hRS : R ⊆ S)
    {a b : Leaf L} (ha : current R = some a) (hb : current S = some b) : a ≤ b := by
  exact ((current_eq_some_iff R a).mp ha).2 b
    (fun h => ((current_eq_some_iff S b).mp hb).1 (hRS h))

def Visible {L : ℕ} (R : Retired L) (v : Node L) : Prop :=
  ∃ leaf, current R = some leaf ∧ InSubtree v leaf

theorem visible_has_unretired_leaf {L : ℕ} {R : Retired L} {v : Node L}
    (h : Visible R v) : (subtree v \ R).Nonempty := by
  obtain ⟨leaf,hc,hv⟩ := h
  exact ⟨leaf,Finset.mem_sdiff.mpr ⟨(mem_subtree _ _).mpr hv,((current_eq_some_iff _ _).mp hc).1⟩⟩

def retireSubtree {L : ℕ} (R : Retired L) (v : Node L) : Retired L := R ∪ subtree v

theorem subset_retireSubtree {L : ℕ} (R : Retired L) (v : Node L) :
    R ⊆ retireSubtree R v := Finset.subset_union_left

theorem unretired_retireSubtree {L : ℕ} (R : Retired L) (v : Node L) :
    unretired (retireSubtree R v) = unretired R \ subtree v := by
  ext leaf
  simp [unretired,retireSubtree,and_assoc]

theorem retirement_progress {L : ℕ} (R : Retired L) (v : Node L)
    (hnew : (subtree v \ R).Nonempty) :
    (unretired (retireSubtree R v)).card < (unretired R).card := by
  rw [unretired_retireSubtree]
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset,?_⟩
  obtain ⟨leaf,hl⟩ := hnew
  have hm := Finset.mem_sdiff.mp hl
  intro hback
  have hx := hback ((mem_unretired _ _).mpr hm.2)
  exact (Finset.mem_sdiff.mp hx).2 hm.1

theorem retirement_gain {L : ℕ} (R : Retired L) (v : Node L) :
    (subtree v \ R).card + R.card = (retireSubtree R v).card := by
  simpa only [retireSubtree,Finset.union_comm] using Finset.card_sdiff_add_card (subtree v) R

section Repair

variable {L : ℕ} {Action : Type*}

/-- A fixed public list supplies the priority. The geometric trigger may
depend on the current retired set, but the target is a genuine tree node. -/
def viable (target : Action → Node L) (trigger : Retired L → Action → Bool)
    (R : Retired L) (a : Action) : Bool :=
  trigger R a && decide ((subtree (target a) \ R).Nonempty)

def chooseRepair (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) : Option Action :=
  priority.find? (viable target trigger R)

theorem chooseRepair_spec (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) {a : Action}
    (ha : chooseRepair priority target trigger R = some a) :
    a ∈ priority ∧ trigger R a = true ∧ (subtree (target a) \ R).Nonempty := by
  have hv := List.find?_some ha
  exact ⟨List.mem_of_find?_eq_some ha,by simpa only [viable,Bool.and_eq_true,decide_eq_true_eq] using hv⟩

theorem chooseRepair_priority (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) {a : Action}
    (ha : chooseRepair priority target trigger R = some a) :
    ∃ before after, priority = before ++ a :: after ∧
      ∀ b ∈ before, viable target trigger R b = false := by
  obtain ⟨_,before,after,he,hprev⟩ := List.find?_eq_some_iff_append.mp ha
  refine ⟨before,after,he,?_⟩
  intro b hb
  have hp := hprev b hb
  cases hv : viable target trigger R b <;> simp_all

theorem chooseRepair_none_iff (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) :
    chooseRepair priority target trigger R = none ↔
      ∀ a ∈ priority, trigger R a = true → subtree (target a) ⊆ R := by
  rw [chooseRepair,List.find?_eq_none]
  constructor
  · intro hn a ha ht leaf hl
    by_contra hr
    have hnew : (subtree (target a) \ R).Nonempty := ⟨leaf,Finset.mem_sdiff.mpr ⟨hl,hr⟩⟩
    exact hn a ha (by simp [viable,ht,hnew])
  · intro hn a ha hv
    have hh : trigger R a = true ∧ (subtree (target a) \ R).Nonempty := by
      simpa only [viable,Bool.and_eq_true,decide_eq_true_eq] using hv
    obtain ⟨leaf,hl⟩ := hh.2
    have hm := Finset.mem_sdiff.mp hl
    exact hm.2 (hn a ha hh.1 hm.1)

/-- The trace records only actual successful repairs. A successful step
retires at least one previously live leaf, independently of its cause. -/
def runRepairs (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) : ℕ → Retired L → Retired L × List Action
  | 0, R => (R,[])
  | fuel+1, R => match chooseRepair priority target trigger R with
      | none => (R,[])
      | some a =>
          let out := runRepairs priority target trigger fuel (retireSubtree R (target a))
          (out.1,a::out.2)

theorem runRepairs_mono (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (fuel : ℕ) (R : Retired L) :
    R ⊆ (runRepairs priority target trigger fuel R).1 := by
  induction fuel generalizing R with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
      cases hc : chooseRepair priority target trigger R with
      | none => simp [runRepairs,hc]
      | some a =>
          exact (subset_retireSubtree R (target a)).trans (by simpa [runRepairs,hc] using ih (retireSubtree R (target a)))

theorem runRepairs_retired_eq (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (fuel : ℕ) (R : Retired L) :
    (runRepairs priority target trigger fuel R).1 = R ∪
      (runRepairs priority target trigger fuel R).2.toFinset.biUnion (fun a => subtree (target a)) := by
  induction fuel generalizing R with
  | zero => simp [runRepairs]
  | succ fuel ih =>
      cases hc : chooseRepair priority target trigger R with
      | none => simp [runRepairs,hc]
      | some a =>
          simpa [runRepairs,hc,retireSubtree,Finset.union_assoc] using ih (retireSubtree R (target a))

theorem runRepairs_trace_mem (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (fuel : ℕ) (R : Retired L) {a : Action}
    (ha : a ∈ (runRepairs priority target trigger fuel R).2) : a ∈ priority := by
  induction fuel generalizing R with
  | zero => simp [runRepairs] at ha
  | succ fuel ih =>
      cases hc : chooseRepair priority target trigger R with
      | none => simp [runRepairs,hc] at ha
      | some b =>
          simp only [runRepairs,hc,List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact (chooseRepair_spec priority target trigger R hc).1
          · exact ih (retireSubtree R (target b)) ha

theorem runRepairs_steps_le (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (fuel : ℕ) (R : Retired L) :
    (runRepairs priority target trigger fuel R).2.length ≤ (unretired R).card := by
  induction fuel generalizing R with
  | zero => simp [runRepairs]
  | succ fuel ih =>
      cases hc : chooseRepair priority target trigger R with
      | none => simp [runRepairs,hc]
      | some a =>
          have hp := retirement_progress R (target a) (chooseRepair_spec priority target trigger R hc).2.2
          have hi := ih (retireSubtree R (target a))
          simpa only [runRepairs,hc,List.length_cons] using (show
            (runRepairs priority target trigger fuel (retireSubtree R (target a))).2.length+1 ≤
              (unretired R).card by omega)

theorem runRepairs_terminal (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (fuel : ℕ) (R : Retired L)
    (hfuel : (unretired R).card ≤ fuel) :
    chooseRepair priority target trigger (runRepairs priority target trigger fuel R).1 = none := by
  induction fuel generalizing R with
  | zero =>
      change chooseRepair priority target trigger R = none
      cases hc : chooseRepair priority target trigger R with
      | none => rfl
      | some a =>
          have hp := retirement_progress R (target a) (chooseRepair_spec priority target trigger R hc).2.2
          omega
  | succ fuel ih =>
      cases hc : chooseRepair priority target trigger R with
      | none => simp only [runRepairs,hc]
      | some a =>
          have hp := retirement_progress R (target a) (chooseRepair_spec priority target trigger R hc).2.2
          have hi := ih (retireSubtree R (target a)) (by omega)
          simpa only [runRepairs,hc] using hi

def repair (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) : Retired L × List Action :=
  runRepairs priority target trigger (8^L) R

theorem repair_terminal (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) :
    chooseRepair priority target trigger (repair priority target trigger R).1 = none := by
  apply runRepairs_terminal
  calc
    (unretired R).card ≤ Fintype.card (Leaf L) := Finset.card_le_univ _
    _ = 8^L := leaf_card L

theorem repair_steps_le (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) :
    (repair priority target trigger R).2.length ≤ 8^L := by
  calc
    _ ≤ (unretired R).card := runRepairs_steps_le priority target trigger _ R
    _ ≤ Fintype.card (Leaf L) := Finset.card_le_univ _
    _ = 8^L := leaf_card L

theorem repair_current_mono (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) {a b : Leaf L}
    (ha : current R = some a)
    (hb : current (repair priority target trigger R).1 = some b) : a ≤ b :=
  current_mono (runRepairs_mono priority target trigger _ R) ha hb

theorem repair_exhaustive (priority : List Action) (target : Action → Node L)
    (trigger : Retired L → Action → Bool) (R : Retired L) :
    ∀ a ∈ priority, trigger (repair priority target trigger R).1 a = true →
      subtree (target a) ⊆ (repair priority target trigger R).1 :=
  (chooseRepair_none_iff priority target trigger _).mp (repair_terminal priority target trigger R)

end Repair

end GradientHessian.FrontierState
