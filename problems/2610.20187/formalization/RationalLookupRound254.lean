import RationalLookupCost254
import NumberedScheduleCost254

open scoped BigOperators
namespace Paper254

/-- Two independent counters: rational arithmetic and integer key comparisons. -/
def mapWithKeyCosts {α β : Type} (f : α→(β×ℕ)×ℕ) : List α→(List β×ℕ)×ℕ
  | []=>(([],0),0)
  | a::xs=>let h:=f a; let tail:=mapWithKeyCosts f xs
           ((h.1.1::tail.1.1,h.1.2+tail.1.2),h.2+tail.2)

theorem mapWithKeyCosts_program {α β : Type} (f : α→(β×ℕ)×ℕ) (xs : List α) :
    (mapWithKeyCosts f xs).1=mapWithCosts (fun x=>(f x).1) xs := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [mapWithKeyCosts,mapWithCosts,ih]

theorem mapWithKeyCosts_keys {α β : Type} (f : α→(β×ℕ)×ℕ) (xs : List α) (C : ℕ)
    (hc : ∀ x∈xs,(f x).2≤C) : (mapWithKeyCosts f xs).2≤xs.length*C := by
  induction xs with
  | nil=>simp [mapWithKeyCosts]
  | cons a xs ih=>
    have ha:=hc a (by simp)
    have ht:=ih (fun x hx=>hc x (by simp [hx]))
    simp only [mapWithKeyCosts,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def keyedLiveSoftmax {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ×ℕ) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let raw:=mapWithKeyCosts (fun e=>
    let we:=w e; let ze:=z e
    let exponential:=countedRationalExp ze.1 (p+4)
    (((e,we.1*exponential.1),exponential.2+1),we.2+ze.2)) (live.sort (·≤·))
  let normalized:=countedNormalize raw.1.1
  let power:=countedRatPow 2 p
  let bump : ℚ×ℕ :=(3/(2*power.1),2)
  let upper:=mapWithCosts (fun e=>((e.1,dyadicCeil (p+1) e.2+bump.1),roundCost+1)) normalized.1
  let out:=countedNormalize upper.1
  ((out.1,raw.1.2+normalized.2+power.2+bump.2+upper.2+out.2),raw.2)

theorem keyedLiveSoftmax_program {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ×ℕ) :
    (keyedLiveSoftmax p roundCost live w z).1=
      countedLiveSoftmax p roundCost live (fun e=>(w e).1) (fun e=>(z e).1) := by
  simp only [keyedLiveSoftmax,mapWithKeyCosts_program,countedLiveSoftmax]

theorem keyedLiveSoftmax_keys {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ×ℕ) (W Z : ℕ) (hw : ∀ e∈live,(w e).2≤W) (hz : ∀ e∈live,(z e).2≤Z) :
    (keyedLiveSoftmax p roundCost live w z).2≤live.card*(W+Z) := by
  apply (mapWithKeyCosts_keys _ _ (W+Z) ?_).trans_eq
  · rw [Finset.length_sort]
  · intro e he
    exact Nat.add_le_add (hw e (by simpa using he)) (hz e (by simpa using he))

def keyedPruneShare {n : ℕ} (w prior : Fin n→ℚ×ℕ) (alpha : ℚ) (next : Finset (Fin n)) :
    (List (Fin n×ℚ)×ℕ)×ℕ :=
  let raw:=mapWithKeyCosts (fun e=>
    let we:=w e; let pe:=prior e
    (((e,(1-alpha)*we.1+alpha*pe.1),4),we.2+pe.2)) (next.sort (·≤·))
  let out:=countedNormalize raw.1.1
  ((out.1,raw.1.2+out.2),raw.2)

theorem keyedPruneShare_program {n : ℕ} (w prior : Fin n→ℚ×ℕ) (alpha : ℚ) (next : Finset (Fin n)) :
    (keyedPruneShare w prior alpha next).1=
      countedPruneShare (fun e=>(w e).1) (fun e=>(prior e).1) alpha next := by
  simp only [keyedPruneShare,mapWithKeyCosts_program,countedPruneShare]

theorem keyedPruneShare_keys {n : ℕ} (w prior : Fin n→ℚ×ℕ) (alpha : ℚ) (next : Finset (Fin n))
    (W P : ℕ) (hw : ∀ e∈next,(w e).2≤W) (hp : ∀ e∈next,(prior e).2≤P) :
    (keyedPruneShare w prior alpha next).2≤next.card*(W+P) := by
  apply (mapWithKeyCosts_keys _ _ (W+P) ?_).trans_eq
  · rw [Finset.length_sort]
  · intro e he
    exact Nat.add_le_add (hw e (by simpa using he)) (hp e (by simpa using he))

def keyedMasterUpdate {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ×ℕ) (alpha : ℚ) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let weighted:=keyedLiveSoftmax p roundCost live w z
  let shared:=keyedPruneShare (countedKeyedLookup 0 weighted.1.1) prior alpha next
  let out:=keyedLiveSoftmax p roundCost next (countedKeyedLookup 0 shared.1.1) (fun _=>(0,0))
  ((out.1.1,weighted.1.2+shared.1.2+out.1.2),weighted.2+shared.2+out.2)

theorem keyedMasterUpdate_program {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ×ℕ) (alpha : ℚ) :
    (keyedMasterUpdate p roundCost live next w z prior alpha).1=
      countedMasterUpdate p roundCost live next (fun e=>(w e).1) (fun e=>(z e).1)
        (fun e=>(prior e).1) alpha := by
  simp only [keyedMasterUpdate,keyedLiveSoftmax_program,keyedPruneShare_program,
    countedKeyedLookup_value,keyedLookup_rational,countedMasterUpdate]

theorem keyedMasterUpdate_keys {n : ℕ} (p roundCost : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ×ℕ) (alpha : ℚ) (W Z P : ℕ)
    (hw : ∀ e∈live,(w e).2≤W) (hz : ∀ e∈live,(z e).2≤Z)
    (hp : ∀ e∈next,(prior e).2≤P) :
    (keyedMasterUpdate p roundCost live next w z prior alpha).2≤
      live.card*(W+Z)+next.card*(live.card+P)+next.card^2 := by
  have hfirst:=keyedLiveSoftmax_keys p roundCost live w z W Z hw hz
  have hlen : (keyedLiveSoftmax p roundCost live w z).1.1.length=live.card := by
    rw [keyedLiveSoftmax_program,countedLiveSoftmax_length]
  have hshare:=keyedPruneShare_keys (countedKeyedLookup 0 (keyedLiveSoftmax p roundCost live w z).1.1)
    prior alpha next live.card P (by
      intro e _
      simpa only [hlen] using (countedKeyedLookup_cost 0 (keyedLiveSoftmax p roundCost live w z).1.1 e)) hp
  have hlen2 : (keyedPruneShare (countedKeyedLookup 0 (keyedLiveSoftmax p roundCost live w z).1.1)
      prior alpha next).1.1.length=next.card := by
    rw [keyedPruneShare_program]
    simp [countedPruneShare,mapWithCosts_length,countedNormalize_length]
  have hlast:=keyedLiveSoftmax_keys p roundCost next
    (countedKeyedLookup 0 (keyedPruneShare (countedKeyedLookup 0 (keyedLiveSoftmax p roundCost live w z).1.1)
      prior alpha next).1.1) (fun _=>(0,0)) next.card 0
    (by
      intro e _
      simpa only [hlen2] using (countedKeyedLookup_cost (0:ℚ)
        (keyedPruneShare (countedKeyedLookup 0 (keyedLiveSoftmax p roundCost live w z).1.1) prior alpha next).1.1 e)) (by simp)
  change _+_+_≤_
  simp only [Nat.add_zero,pow_two] at *
  omega

end Paper254
#print axioms Paper254.keyedMasterUpdate_program
#print axioms Paper254.keyedMasterUpdate_keys
