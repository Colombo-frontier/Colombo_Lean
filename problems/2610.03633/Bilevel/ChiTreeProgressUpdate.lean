import Bilevel.ChiTreeProgressCounter

/-! One terminal success changes at most one prefix at each depth, and
advances each such prefix by at most one column. Ancestor disclosures are
therefore counted explicitly, not silently identified with a terminal one. -/
namespace Bilevel.ChiTreeProgress

theorem nodePrefix_mono (n : ℕ → ℕ) (d j : ℕ) : Monotone (nodePrefix n d j) := by
  intro q q' hq
  cases d with
  | zero => exact min_le_min_left _ hq
  | succ d => exact min_le_min_left _ (Nat.div_le_div_right hq)

theorem nodePrefix_success_le (n : ℕ → ℕ) (d j q : ℕ) :
    nodePrefix n d j (q+1)≤nodePrefix n d j q+1 := by
  cases d with
  | zero => change min (n j+1) (q+1)≤min (n j+1) q+1;omega
  | succ d =>
    let cap := capacity n d (j+1)
    have hc : 0<cap := capacity_pos n d (j+1)
    have hs := Nat.div_add_mod q cap
    have hm := Nat.mod_lt q hc
    have hlt : q+1<(q/cap+2)*cap := by
      rw [Nat.mul_comm cap (q/cap)] at hs
      rw [Nat.add_mul]
      nlinarith
    have hd := (Nat.div_lt_iff_lt_mul hc).mpr hlt
    change min (n j+1) ((q+1)/cap)≤min (n j+1) (q/cap)+1
    omega

theorem nodeBudget_success_or_eq (n : ℕ → ℕ) (d j q : ℕ) (I : List ℕ) :
    nodeBudget n d j (q+1) I=nodeBudget n d j q I ∨
      nodeBudget n d j (q+1) I=nodeBudget n d j q I+1 := by
  induction I generalizing d j q with
  | nil => exact Or.inr rfl
  | cons i I ih =>
    simp only [nodeBudget,childBudget_success _ _ _ (capacity_pos n (d-1) (j+1))]
    by_cases hi : i=q/capacity n (d-1) (j+1)
    · simpa only [if_pos hi] using ih (d-1) (j+1) (childBudget (capacity n (d-1) (j+1)) i q)
    · simp only [if_neg hi,add_zero,true_or]

theorem nodeBudget_changed_path_unique (n : ℕ → ℕ) (d j q : ℕ) (I K : List ℕ)
    (hlen : I.length=K.length)
    (hI : nodeBudget n d j (q+1) I≠nodeBudget n d j q I)
    (hK : nodeBudget n d j (q+1) K≠nodeBudget n d j q K) : I=K := by
  induction I generalizing d j q K with
  | nil => exact (List.length_eq_zero_iff.mp (by simpa using hlen.symm)).symm
  | cons i I ih =>
    cases K with
    | nil => simp only [List.length_cons,List.length_nil] at hlen;omega
    | cons k K =>
      have hi : i=q/capacity n (d-1) (j+1) := by
        by_cases hn : i=q/capacity n (d-1) (j+1)
        · exact hn
        exfalso
        apply hI
        simp only [nodeBudget,childBudget_success _ _ _ (capacity_pos n (d-1) (j+1)),if_neg hn,add_zero]
      have hk : k=q/capacity n (d-1) (j+1) := by
        by_cases hn : k=q/capacity n (d-1) (j+1)
        · exact hn
        exfalso
        apply hK
        simp only [nodeBudget,childBudget_success _ _ _ (capacity_pos n (d-1) (j+1)),if_neg hn,add_zero]
      have hik : i=k := hi.trans hk.symm
      rw [←hik] at hK
      simp only [nodeBudget,childBudget_success _ _ _ (capacity_pos n (d-1) (j+1)),if_pos hi,if_true] at hI hK
      exact congrArg₂ List.cons hik (ih (d-1) (j+1) _ K (by simpa using hlen) hI hK)

theorem counter_success_bounds (n : ℕ → ℕ) (total q j : ℕ) (I : List ℕ) :
    counter n total q j I≤counter n total (q+1) j I ∧
      counter n total (q+1) j I≤counter n total q j I+1 := by
  by_cases hI : I.length=j
  · rw [counter_at n total q j I hI,counter_at n total (q+1) j I hI]
    rcases nodeBudget_success_or_eq n total 0 q I with he|he
    · rw [he];omega
    · rw [he]
      exact ⟨nodePrefix_mono n _ _ (Nat.le_succ _),nodePrefix_success_le n _ _ _⟩
  · simp only [counter,if_neg hI,Nat.zero_le,zero_add,le_refl,and_self]

theorem counter_changed_path_unique (n : ℕ → ℕ) (total q j : ℕ) (I K : List ℕ)
    (hIlen : I.length=j) (hKlen : K.length=j)
    (hI : counter n total (q+1) j I≠counter n total q j I)
    (hK : counter n total (q+1) j K≠counter n total q j K) : I=K := by
  apply nodeBudget_changed_path_unique n total 0 q I K (hIlen.trans hKlen.symm)
  · intro he
    apply hI
    rw [counter_at n total (q+1) j I hIlen,counter_at n total q j I hIlen,he]
  · intro he
    apply hK
    rw [counter_at n total (q+1) j K hKlen,counter_at n total q j K hKlen,he]

end Bilevel.ChiTreeProgress
