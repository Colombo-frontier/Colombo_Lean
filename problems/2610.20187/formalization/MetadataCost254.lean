import RationalCompactMaster254
import Mathlib.Data.List.Sort

namespace Paper254

def countedOrderedInsert {α : Type} [LinearOrder α] (a : α) : List α→List α×ℕ
  | []=>([a],0)
  | b::xs=>if a≤b then (a::b::xs,1) else
      let out:=countedOrderedInsert a xs
      (b::out.1,out.2+1)

theorem countedOrderedInsert_value {α : Type} [LinearOrder α] (a : α) (xs : List α) :
    (countedOrderedInsert a xs).1=List.orderedInsert (·≤·) a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => by_cases h : a ≤ b <;> simp [countedOrderedInsert,List.orderedInsert,ih,h]

theorem countedOrderedInsert_cost {α : Type} [LinearOrder α] (a : α) (xs : List α) :
    (countedOrderedInsert a xs).2≤xs.length := by
  induction xs with
  | nil => simp [countedOrderedInsert]
  | cons b xs ih => simp only [countedOrderedInsert,List.length_cons]; split_ifs <;> omega

def countedInsertionSort {α : Type} [LinearOrder α] : List α→List α×ℕ
  | []=>([],0)
  | a::xs=>let tail:=countedInsertionSort xs
           let out:=countedOrderedInsert a tail.1
           (out.1,tail.2+out.2)

theorem countedInsertionSort_value {α : Type} [LinearOrder α] (xs : List α) :
    (countedInsertionSort xs).1=List.insertionSort (·≤·) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [countedInsertionSort,countedOrderedInsert_value,ih,List.insertionSort]

theorem countedInsertionSort_cost {α : Type} [LinearOrder α] (xs : List α) :
    (countedInsertionSort xs).2≤xs.length*xs.length := by
  induction xs with
  | nil => simp [countedInsertionSort]
  | cons a xs ih =>
    have hh:=countedOrderedInsert_cost a (countedInsertionSort xs).1
    have hl : (countedInsertionSort xs).1.length=xs.length := by
      rw [countedInsertionSort_value,List.length_insertionSort]
    rw [hl] at hh
    simp only [countedInsertionSort,List.length_cons,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

/-- Any concrete list representation of a finite set has a certified
quadratic-comparison implementation of the exact sorted key list. -/
theorem countedInsertionSort_finset {α : Type} [LinearOrder α] (xs : List α) (s : Finset α)
    (hxs : (xs:Multiset α)=s.val) : (countedInsertionSort xs).1=s.sort (·≤·) := by
  rw [countedInsertionSort_value,←List.mergeSort_eq_insertionSort]
  rw [←Multiset.coe_sort,hxs,Finset.sort_val]

def countedContains {α : Type} [DecidableEq α] (a : α) : List α→Bool×ℕ
  | []=>(false,0)
  | b::xs=>if a=b then (true,1) else
      let out:=countedContains a xs
      (out.1,out.2+1)

theorem countedContains_value {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    (countedContains a xs).1=true ↔ a∈xs := by
  induction xs generalizing a with
  | nil => simp [countedContains]
  | cons b xs ih => by_cases h:a=b <;> simp [countedContains,h,ih]

theorem countedContains_cost {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    (countedContains a xs).2≤xs.length := by
  induction xs with
  | nil => simp [countedContains]
  | cons b xs ih => simp only [countedContains,List.length_cons]; split_ifs <;> omega

def countedDedup {α : Type} [DecidableEq α] : List α→List α×ℕ
  | []=>([],0)
  | a::xs=>let tail:=countedDedup xs
           let found:=countedContains a tail.1
           (if found.1=true then tail.1 else a::tail.1,tail.2+found.2)

theorem countedDedup_mem {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a∈(countedDedup xs).1 ↔ a∈xs := by
  induction xs generalizing a with
  | nil => simp [countedDedup]
  | cons b xs ih =>
    simp only [countedDedup,countedContains_value]
    split_ifs with h
    · have hb : b∈xs := (ih b).mp h
      simp only [ih,List.mem_cons]
      aesop
    · simp only [List.mem_cons,ih]

theorem countedDedup_nodup {α : Type} [DecidableEq α] (xs : List α) : (countedDedup xs).1.Nodup := by
  induction xs with
  | nil => simp [countedDedup]
  | cons a xs ih =>
    simp only [countedDedup,countedContains_value]
    split_ifs with h
    · exact ih
    · exact List.nodup_cons.mpr ⟨h,ih⟩

theorem countedDedup_length {α : Type} [DecidableEq α] (xs : List α) :
    (countedDedup xs).1.length≤xs.length := by
  induction xs with
  | nil => simp [countedDedup]
  | cons a xs ih =>
    simp only [countedDedup,List.length_cons]
    split_ifs
    · exact ih.trans (Nat.le_succ _)
    · exact Nat.succ_le_succ ih

theorem countedDedup_cost {α : Type} [DecidableEq α] (xs : List α) :
    (countedDedup xs).2≤xs.length*xs.length := by
  induction xs with
  | nil => simp [countedDedup]
  | cons a xs ih =>
    have hh:=(countedContains_cost a (countedDedup xs).1).trans (countedDedup_length xs)
    simp only [countedDedup,List.length_cons,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

theorem countedDedup_toFinset {α : Type} [DecidableEq α] (xs : List α) :
    (countedDedup xs).1.toFinset=xs.toFinset := by ext a; simp [countedDedup_mem]

def countedUniqueSort {α : Type} [LinearOrder α] (xs : List α) : List α×ℕ :=
  let unique:=countedDedup xs
  let sorted:=countedInsertionSort unique.1
  (sorted.1,unique.2+sorted.2)

theorem countedUniqueSort_value {α : Type} [LinearOrder α] (xs : List α) :
    (countedUniqueSort xs).1=xs.toFinset.sort (·≤·) := by
  apply countedInsertionSort_finset
  have hh:=countedDedup_toFinset xs
  have hv:=congrArg Finset.val hh
  simpa only [List.toFinset_val,Multiset.coe_dedup,List.dedup_eq_self.mpr (countedDedup_nodup xs)] using hv

theorem countedUniqueSort_cost {α : Type} [LinearOrder α] (xs : List α) :
    (countedUniqueSort xs).2≤2*xs.length*xs.length := by
  have hu:=countedDedup_cost xs
  have hs:=countedInsertionSort_cost (countedDedup xs).1
  have hl:=countedDedup_length xs
  have hm:=Nat.mul_self_le_mul_self hl
  change (countedDedup xs).2+(countedInsertionSort (countedDedup xs).1).2≤_
  nlinarith

end Paper254
#print axioms Paper254.countedInsertionSort_finset
#print axioms Paper254.countedUniqueSort_value
#print axioms Paper254.countedUniqueSort_cost
