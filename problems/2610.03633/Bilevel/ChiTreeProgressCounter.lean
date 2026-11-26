import Bilevel.ChiTreeProgressArithmetic

/-! A concrete public counter on every prefix. The only input state is the
number of terminal successes; node budgets are allocated in lexicographic
order. No support or oracle property enters these definitions. -/
namespace Bilevel.ChiTreeProgress

def nodePrefix (n : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,j,q => min (n j+1) q
  | d+1,j,q => parentPrefix (n j+1) (capacity n d (j+1)) q

theorem nodePrefix_le (n : ℕ → ℕ) (d j q : ℕ) : nodePrefix n d j q≤n j+1 := by
  cases d <;> exact Nat.min_le_left _ _

theorem nodePrefix_complete (n : ℕ → ℕ) (d j q : ℕ) (hq : capacity n d j≤q) :
    nodePrefix n d j q=n j+1 := by
  cases d with
  | zero => exact Nat.min_eq_left hq
  | succ d => exact Nat.min_eq_left ((Nat.le_div_iff_mul_le (capacity_pos n d (j+1))).mpr hq)

theorem nodePrefix_incomplete (n : ℕ → ℕ) (d j q : ℕ) (hq : q<capacity n d j) :
    nodePrefix n d j q≤n j := by
  cases d with
  | zero => exact (Nat.min_le_right _ _).trans (by exact Nat.le_of_lt_succ hq)
  | succ d =>
    have hh : q/capacity n d (j+1)<n j+1 :=
      (Nat.div_lt_iff_lt_mul (capacity_pos n d (j+1))).mpr hq
    exact (Nat.min_le_right _ _).trans (Nat.le_of_lt_succ hh)

def nodeBudget (n : ℕ → ℕ) : ℕ → ℕ → ℕ → List ℕ → ℕ
  | _,_,q,[] => q
  | d,j,q,i::I => nodeBudget n (d-1) (j+1)
      (childBudget (capacity n (d-1) (j+1)) i q) I

theorem nodeBudget_child (n : ℕ → ℕ) (d j q : ℕ) (I : List ℕ) (i : ℕ) :
    nodeBudget n d j q (I++[i])=
      childBudget (capacity n (d-(I.length+1)) (j+I.length+1)) i (nodeBudget n d j q I) := by
  induction I generalizing d j q with
  | nil => simp [nodeBudget]
  | cons k I ih =>
    simp only [List.cons_append,nodeBudget,ih,List.length_cons]
    congr 2 <;> omega

def counter (n : ℕ → ℕ) (total q j : ℕ) (I : List ℕ) : ℕ :=
  if I.length=j then nodePrefix n (total-j) j (nodeBudget n total 0 q I) else 0

theorem counter_at (n : ℕ → ℕ) (total q j : ℕ) (I : List ℕ) (hI : I.length=j) :
    counter n total q j I=nodePrefix n (total-j) j (nodeBudget n total 0 q I) := if_pos hI

theorem counter_child_budget (n : ℕ → ℕ) (total q j : ℕ) (I : List ℕ)
    (hI : I.length=j) (i : ℕ) :
    nodeBudget n total 0 q (I++[i])=
      childBudget (capacity n (total-(j+1)) (j+1)) i (nodeBudget n total 0 q I) := by
  rw [nodeBudget_child,hI]
  simp only [Nat.zero_add]

theorem counter_future (n : ℕ → ℕ) (total q j : ℕ) (I : List ℕ)
    (hj : j<total) (i : Fin (n j+1)) (hi : counter n total q j I ≤ i.val) :
    counter n total q (j+1) (I++[i.val])≤n (j+1) := by
  by_cases hI : I.length=j
  · have hIc : (I++[i.val]).length=j+1 := by simp [hI]
    rw [counter_at n total q (j+1) _ hIc,counter_child_budget n total q j I hI]
    apply nodePrefix_incomplete
    apply future_child_incomplete (n j+1) _ _ i.val (capacity_pos _ _ _) i.isLt
    have hd : total-j=(total-(j+1))+1 := by omega
    simpa only [counter_at n total q j I hI,hd,nodePrefix] using hi
  · have hIc : (I++[i.val]).length≠j+1 := by simp only [List.length_append,List.length_singleton];omega
    simp only [counter,if_neg hIc,Nat.zero_le]

end Bilevel.ChiTreeProgress
