import SparseHistoryCost254
import RationalTaylorCost254
import RationalMasterUpdate254

open scoped BigOperators
namespace Paper254

def rationalLookup {n : ℕ} (entries : List (Fin n×ℚ)) (j : Fin n) : ℚ :=
  match entries with
  | []=>0
  | (i,v)::xs=>if i=j then v else rationalLookup xs j

theorem rationalLookup_map {n : ℕ} (xs : List (Fin n)) (f : Fin n→ℚ) (j : Fin n) :
    rationalLookup (xs.map (fun i=>(i,f i))) j=if j∈xs then f j else 0 := by
  induction xs with
  | nil => simp [rationalLookup]
  | cons i xs ih =>
    by_cases h : i=j
    · subst i; simp [rationalLookup]
    · simp [rationalLookup,h,ih,Ne.symm h]

theorem rational_sum_sort {n : ℕ} (s : Finset (Fin n)) (f : Fin n→ℚ) :
    ((s.sort (·≤·)).map f).sum=∑ i∈s,f i := by
  change ((↑(s.sort (·≤·)):Multiset (Fin n)).map f).sum=_
  rw [Finset.sort_eq]
  rfl

def countedRationalSum : List ℚ→ℚ×ℕ
  | []=>(0,0)
  | x::xs=>let tail:=countedRationalSum xs; (x+tail.1,tail.2+1)

theorem countedRationalSum_spec (xs : List ℚ) : countedRationalSum xs=(xs.sum,xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countedRationalSum,ih]

/-- One cached normalizer, followed by one division per stored entry. -/
def countedNormalize {n : ℕ} (entries : List (Fin n×ℚ)) : List (Fin n×ℚ)×ℕ :=
  let total:=countedRationalSum (entries.map Prod.snd)
  let out:=mapWithCosts (fun e=>((e.1,e.2/total.1),1)) entries
  (out.1,total.2+out.2)

theorem countedNormalize_value {n : ℕ} (entries : List (Fin n×ℚ)) :
    (countedNormalize entries).1=entries.map (fun e=>(e.1,e.2/(entries.map Prod.snd).sum)) := by
  simp [countedNormalize,mapWithCosts_values,countedRationalSum_spec]

theorem mapWithCosts_constant {α β : Type} (f : α→β) (c : ℕ) (xs : List α) :
    (mapWithCosts (fun x=>(f x,c)) xs).2=c*xs.length := by
  induction xs with
  | nil => simp [mapWithCosts]
  | cons x xs ih => simp [mapWithCosts,ih,Nat.mul_add,Nat.add_comm]

theorem countedNormalize_cost {n : ℕ} (entries : List (Fin n×ℚ)) :
    (countedNormalize entries).2=2*entries.length := by
  simp [countedNormalize,countedRationalSum_spec,mapWithCosts_constant]
  omega

def countedLiveSoftmax {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) : List (Fin n×ℚ)×ℕ :=
  let raw:=mapWithCosts (fun e=>
    let exponential:=countedRationalExp (z e) (p+4)
    ((e,w e*exponential.1),exponential.2+1)) (live.sort (·≤·))
  let normalized:=countedNormalize raw.1
  let power:=countedRatPow 2 p
  let bump : ℚ×ℕ := (3/(2*power.1),2)
  let upper:=mapWithCosts (fun e=>((e.1,dyadicCeil (p+1) e.2+bump.1),roundCost+1)) normalized.1
  let out:=countedNormalize upper.1
  (out.1,raw.2+normalized.2+power.2+bump.2+upper.2+out.2)

theorem countedLiveSoftmax_value {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) (hsupport : ∀ j,j∉live → w j=0) :
    rationalLookup (countedLiveSoftmax p roundCost live w z).1=rationalLiveSoftmax p live w z := by
  let f:=fun e=>w e*rationalExp (z e) (p+4)
  have hsum : ∑ e∈live,f e=∑ e,f e := Finset.sum_subset (Finset.subset_univ _)
    (by intro e he hn; simp [f,hsupport e hn])
  have hraw : (mapWithCosts (fun e=>
      let exponential:=countedRationalExp (z e) (p+4)
      ((e,w e*exponential.1),exponential.2+1)) (live.sort (·≤·))).1=
      (live.sort (·≤·)).map (fun e=>(e,f e)) := by
    simp [mapWithCosts_values,countedRationalExp_value,f]
  have hnorm : (countedNormalize ((live.sort (·≤·)).map (fun e=>(e,f e)))).1=
      (live.sort (·≤·)).map (fun e=>(e,rationalSoftmaxApprox p w z e)) := by
    simp only [countedNormalize_value,List.map_map,Function.comp_def]
    rw [rational_sum_sort,hsum]
    rfl
  have hmass : ∑ e∈live,rationalUpperMass p w z e=∑ e,rationalLiveMass p live w z e := by
    simp only [rationalLiveMass,Finset.sum_ite_mem,Finset.univ_inter]
  funext j
  simp only [countedLiveSoftmax,hraw,hnorm,mapWithCosts_values,countedRatPow_spec,
    countedNormalize_value,List.map_map,Function.comp_def]
  change rationalLookup ((live.sort (·≤·)).map (fun e=>
    (e,rationalUpperMass p w z e/((live.sort (·≤·)).map (rationalUpperMass p w z)).sum))) j=_
  rw [rational_sum_sort,hmass,rationalLookup_map]
  by_cases hj : j∈live <;> simp [rationalLiveSoftmax,rationalLiveMass,hj]

theorem mapWithCosts_length {α β : Type} (f : α→β×ℕ) (xs : List α) :
    (mapWithCosts f xs).1.length=xs.length := by rw [mapWithCosts_values,List.length_map]

theorem countedNormalize_length {n : ℕ} (entries : List (Fin n×ℚ)) :
    (countedNormalize entries).1.length=entries.length := by rw [countedNormalize_value,List.length_map]

theorem mapWithCosts_sum {α β : Type} (f : α→β×ℕ) (xs : List α) :
    (mapWithCosts f xs).2=(xs.map (fun x=>(f x).2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mapWithCosts,List.map_cons,List.sum_cons,ih]

theorem countedLiveSoftmax_cost {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) :
    (countedLiveSoftmax p roundCost live w z).2=
      live.card*(3*(p+7)+roundCost+6)+p+2 := by
  simp only [countedLiveSoftmax,countedNormalize_cost,mapWithCosts_length,countedNormalize_length,
    countedRatPow_spec,mapWithCosts_sum,countedRationalExp_cost]
  simp only [List.map_const',List.sum_replicate,Finset.length_sort,nsmul_eq_mul]
  simp only [countedNormalize_length,mapWithCosts_length,Finset.length_sort]
  norm_cast
  ring

theorem rationalMasterUpdate_congr_live {n : ℕ} (p : ℕ) (live next : Finset (Fin n))
    (w z z' prior : Fin n→ℚ) (alpha : ℚ) (hsupport : ∀ j,j∉live → w j=0)
    (hz : ∀ j∈live,z j=z' j) :
    rationalMasterUpdate p live next w z prior alpha=rationalMasterUpdate p live next w z' prior alpha := by
  have hprod : ∀ j,w j*rationalExp (z j) (p+4)=w j*rationalExp (z' j) (p+4) := by
    intro j
    by_cases hj : j∈live
    · rw [hz j hj]
    · simp [hsupport j hj]
  have hsoft : ∀ j,rationalSoftmaxApprox p w z j=rationalSoftmaxApprox p w z' j := by
    intro j
    simp only [rationalSoftmaxApprox,hprod]
  have hupper : ∀ j,rationalUpperMass p w z j=rationalUpperMass p w z' j := by
    intro j
    simp only [rationalUpperMass,hsoft]
  have hlive : rationalLiveSoftmax p live w z=rationalLiveSoftmax p live w z' := by
    funext j
    simp only [rationalLiveSoftmax,rationalLiveMass,hupper]
  simp only [rationalMasterUpdate,hlive]

def countedPruneShare {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    List (Fin n×ℚ)×ℕ :=
  let raw:=mapWithCosts (fun e=>((e,(1-alpha)*w e+alpha*prior e),4)) (next.sort (·≤·))
  let out:=countedNormalize raw.1
  (out.1,raw.2+out.2)

theorem countedPruneShare_value {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    rationalLookup (countedPruneShare w prior alpha next).1=rationalPruneShare w prior alpha next := by
  have hsum : ∑ e∈next,((1-alpha)*w e+alpha*prior e)=∑ e,rationalPrunedMass w prior alpha next e := by
    simp only [rationalPrunedMass,Finset.sum_ite_mem,Finset.univ_inter]
  funext j
  simp only [countedPruneShare,countedNormalize_value,mapWithCosts_values,List.map_map,Function.comp_def]
  rw [rational_sum_sort,hsum,rationalLookup_map]
  by_cases hj : j∈next <;> simp [rationalPruneShare,rationalPrunedMass,hj]

theorem countedPruneShare_cost {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    (countedPruneShare w prior alpha next).2=6*next.card := by
  simp only [countedPruneShare,mapWithCosts_constant,countedNormalize_cost,mapWithCosts_length,
    Finset.length_sort]
  ring

def countedMasterUpdate {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) : List (Fin n×ℚ)×ℕ :=
  let weighted:=countedLiveSoftmax p roundCost live w z
  let shared:=countedPruneShare (rationalLookup weighted.1) prior alpha next
  let out:=countedLiveSoftmax p roundCost next (rationalLookup shared.1) (fun _=>0)
  (out.1,weighted.2+shared.2+out.2)

theorem countedMasterUpdate_value {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) (hsupport : ∀ j,j∉live → w j=0) :
    rationalLookup (countedMasterUpdate p roundCost live next w z prior alpha).1=
      rationalMasterUpdate p live next w z prior alpha := by
  have hs : ∀ j,j∉next →
      rationalLookup (countedPruneShare
        (rationalLookup (countedLiveSoftmax p roundCost live w z).1) prior alpha next).1 j=0 := by
    rw [countedPruneShare_value]
    intro j hj
    simp [rationalPruneShare,rationalPrunedMass,hj]
  unfold countedMasterUpdate
  rw [countedLiveSoftmax_value _ _ _ _ _ hs,countedPruneShare_value,
    countedLiveSoftmax_value _ _ _ _ _ hsupport]
  rfl

theorem countedMasterUpdate_cost {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) :
    (countedMasterUpdate p roundCost live next w z prior alpha).2=
      live.card*(3*(p+7)+roundCost+6)+next.card*(3*(p+7)+roundCost+12)+2*p+4 := by
  simp only [countedMasterUpdate,countedLiveSoftmax_cost,countedPruneShare_cost]
  ring

theorem countedLiveSoftmax_length {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) : (countedLiveSoftmax p roundCost live w z).1.length=live.card := by
  simp only [countedLiveSoftmax,countedNormalize_length,mapWithCosts_length,Finset.length_sort]

theorem countedMasterUpdate_length {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) :
    (countedMasterUpdate p roundCost live next w z prior alpha).1.length=next.card := by
  simp only [countedMasterUpdate,countedLiveSoftmax_length]

end Paper254
#print axioms Paper254.countedLiveSoftmax_value
#print axioms Paper254.countedLiveSoftmax_cost
#print axioms Paper254.rationalMasterUpdate_congr_live
#print axioms Paper254.countedMasterUpdate_value
#print axioms Paper254.countedMasterUpdate_cost
