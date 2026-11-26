import MetadataCost254
import StandardRationalSchedule254

namespace Paper254

def countedNatPowTwo : ℕ→ℕ×ℕ
  | 0=>(1,0)
  | k+1=>let p:=countedNatPowTwo k; (2*p.1,p.2+1)

theorem countedNatPowTwo_spec (k : ℕ) : countedNatPowTwo k=(2^k,k) := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp [countedNatPowTwo,ih,pow_succ,Nat.mul_comm]

def countedAny {α : Type} (f : α→Bool×ℕ) : List α→Bool×ℕ
  | []=>(false,0)
  | a::xs=>let h:=f a; let tail:=countedAny f xs; (h.1||tail.1,h.2+tail.2+1)

theorem countedAny_value {α : Type} (f : α→Bool×ℕ) (xs : List α) :
    (countedAny f xs).1=true ↔ ∃ x∈xs,(f x).1=true := by
  induction xs with
  | nil=>simp [countedAny]
  | cons a xs ih=>simp [countedAny,ih]

theorem countedAny_cost {α : Type} (f : α→Bool×ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs,(f x).2≤C) : (countedAny f xs).2≤xs.length*(C+1) := by
  induction xs with
  | nil=>simp [countedAny]
  | cons a xs ih=>
    have ha:=h a (by simp)
    have ht:=ih (fun x hx=>h x (by simp [hx]))
    simp only [countedAny,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedActiveTest (t i : ℕ) : Bool×ℕ :=
  let tests:=countedAny (fun k=>
    let p:=countedNatPowTwo k
    (decide (i%p.1=0 ∧ t-i≤4*p.1),p.2+5)) (List.range (Nat.log 2 t+1))
  (decide (1 ≤ i ∧ i ≤ t) && tests.1,tests.2+2)

theorem countedActiveTest_value (t i : ℕ) :
    (countedActiveTest t i).1=true ↔ boundedHistoryActive t i := by
  simp [countedActiveTest,countedAny_value,countedNatPowTwo_spec,boundedHistoryActive,and_assoc]

theorem countedActiveTest_cost (t i : ℕ) :
    (countedActiveTest t i).2≤(Nat.log 2 t+1)*(Nat.log 2 t+7)+2 := by
  have hh:=countedAny_cost (fun k=>
    let p:=countedNatPowTwo k
    (decide (i%p.1=0 ∧ t-i≤4*p.1),p.2+5)) (List.range (Nat.log 2 t+1))
    (Nat.log 2 t+6) (by intro k hk; simp only [countedNatPowTwo_spec]; have:=List.mem_range.mp hk; omega)
  simpa only [countedActiveTest,List.length_range,Nat.add_assoc] using Nat.add_le_add_right hh 2

def countedFilter {α : Type} (f : α→Bool×ℕ) : List α→List α×ℕ
  | []=>([],0)
  | a::xs=>let h:=f a; let tail:=countedFilter f xs
           (if h.1 then a::tail.1 else tail.1,h.2+tail.2+1)

theorem countedFilter_value {α : Type} (f : α→Bool×ℕ) (xs : List α) :
    (countedFilter f xs).1=xs.filter (fun x=>(f x).1) := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [countedFilter,List.filter_cons,ih]

theorem countedFilter_cost {α : Type} (f : α→Bool×ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs,(f x).2≤C) : (countedFilter f xs).2≤xs.length*(C+1) := by
  induction xs with
  | nil=>simp [countedFilter]
  | cons a xs ih=>
    have ha:=h a (by simp)
    have ht:=ih (fun x hx=>h x (by simp [hx]))
    simp only [countedFilter,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedCandidateList (t : ℕ) : List ℕ×ℕ :=
  mapWithCosts (fun kq : ℕ×ℕ=>
    let p:=countedNatPowTwo kq.1
    (t-(p.1*kq.2+t%p.1),p.2+4))
    ((List.range (Nat.log 2 t+1)).product (List.range 5))

theorem countedCandidateList_length (t : ℕ) :
    (countedCandidateList t).1.length=5*(Nat.log 2 t+1) := by
  simp [countedCandidateList,mapWithCosts_values,List.product,List.length_flatMap,Nat.mul_comm]

theorem countedCandidateList_finset (t : ℕ) :
    (countedCandidateList t).1.toFinset=shortHistoryCandidates t := by
  ext i
  simp [countedCandidateList,mapWithCosts_values,countedNatPowTwo_spec,shortHistoryCandidates]

theorem countedCandidateList_cost (t : ℕ) :
    (countedCandidateList t).2≤5*(Nat.log 2 t+1)*(Nat.log 2 t+5) := by
  have hh:=mapWithCosts_bound (fun kq : ℕ×ℕ=>
    let p:=countedNatPowTwo kq.1
    (t-(p.1*kq.2+t%p.1),p.2+4))
    ((List.range (Nat.log 2 t+1)).product (List.range 5)) (Nat.log 2 t+5) (by
      intro kq hk
      have h:=List.mem_range.mp (List.mem_product.mp hk).1
      simp only [countedNatPowTwo_spec]
      omega)
  simpa [countedCandidateList,List.product,List.length_flatMap,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh

/-- The complete short-history enumerator performs no scan of past birth times.
Its comparisons, modular tests, and sorting are instrumented separately from
the rational arithmetic of the learner. -/
def countedShortHistoryList (t : ℕ) : List ℕ×ℕ :=
  let candidates:=countedCandidateList t
  let active:=countedFilter (countedActiveTest t) candidates.1
  let sorted:=countedUniqueSort active.1
  (sorted.1,candidates.2+active.2+sorted.2)

theorem countedShortHistoryList_value (t : ℕ) :
    (countedShortHistoryList t).1=(shortActiveHistories t).sort (·≤·) := by
  change (countedUniqueSort _).1=_
  rw [countedUniqueSort_value,countedFilter_value]
  congr 1
  ext i
  simp only [List.mem_toFinset,List.mem_filter,countedActiveTest_value,shortActiveHistories,Finset.mem_filter]
  have hh:=congrArg (fun s : Finset ℕ=>i∈s) (countedCandidateList_finset t)
  exact Iff.of_eq (by simpa only [List.mem_toFinset] using congrArg (fun P=>P ∧ boundedHistoryActive t i) hh)

theorem countedShortHistoryList_cost (t : ℕ) :
    (countedShortHistoryList t).2≤
      5*(Nat.log 2 t+1)*(Nat.log 2 t+5)+
      5*(Nat.log 2 t+1)*((Nat.log 2 t+1)*(Nat.log 2 t+7)+3)+
      2*(5*(Nat.log 2 t+1))^2 := by
  have hc:=countedCandidateList_cost t
  have hf:=countedFilter_cost (countedActiveTest t) (countedCandidateList t).1
    ((Nat.log 2 t+1)*(Nat.log 2 t+7)+2) (fun i _=>countedActiveTest_cost t i)
  rw [countedCandidateList_length] at hf
  have hs:=countedUniqueSort_cost (countedFilter (countedActiveTest t) (countedCandidateList t).1).1
  have hl : (countedFilter (countedActiveTest t) (countedCandidateList t).1).1.length≤5*(Nat.log 2 t+1) := by
    rw [countedFilter_value,←countedCandidateList_length t]
    exact List.length_filter_le _ _
  have hm:=Nat.mul_self_le_mul_self hl
  change (countedCandidateList t).2+(countedFilter (countedActiveTest t) (countedCandidateList t).1).2+
    (countedUniqueSort (countedFilter (countedActiveTest t) (countedCandidateList t).1).1).2≤_
  nlinarith

end Paper254
#print axioms Paper254.countedShortHistoryList_value
#print axioms Paper254.countedShortHistoryList_cost
