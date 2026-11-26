import ShortScheduleCost254

namespace Paper254

def countedFlatMap {α β : Type} (f : α→List β×ℕ) : List α→List β×ℕ
  | []=>([],0)
  | a::xs=>let h:=f a; let tail:=countedFlatMap f xs
           (h.1++tail.1,h.2+h.1.length+tail.2)

theorem countedFlatMap_value {α β : Type} (f : α→List β×ℕ) (xs : List α) :
    (countedFlatMap f xs).1=xs.flatMap (fun x=>(f x).1) := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp [countedFlatMap,ih]

theorem countedFlatMap_cost {α β : Type} (f : α→List β×ℕ) (xs : List α) (C L : ℕ)
    (hc : ∀ x∈xs,(f x).2≤C) (hl : ∀ x∈xs,(f x).1.length≤L) :
    (countedFlatMap f xs).2≤xs.length*(C+L) := by
  induction xs with
  | nil=>simp [countedFlatMap]
  | cons a xs ih=>
    have ha:=hc a (by simp)
    have hb:=hl a (by simp)
    have ht:=ih (fun x hx=>hc x (by simp [hx])) (fun x hx=>hl x (by simp [hx]))
    simp only [countedFlatMap,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedHistoryKeys (T K i : ℕ) : List (Fin ((T+1)*(K+1)))×ℕ :=
  if h : 0 < i ∧ i ≤ T+1 then
    let keys:=mapWithCosts (fun k : Fin (K+1)=>
      ((numberedExpertEquiv T K) (⟨i-1,by omega⟩,k),2)) (List.finRange (K+1))
    (keys.1,keys.2+3)
  else ([],2)

theorem countedHistoryKeys_length (T K i : ℕ) :
    (countedHistoryKeys T K i).1.length≤K+1 := by
  simp only [countedHistoryKeys]
  split_ifs <;> simp [mapWithCosts_values]

theorem countedHistoryKeys_cost (T K i : ℕ) :
    (countedHistoryKeys T K i).2≤2*(K+1)+3 := by
  simp only [countedHistoryKeys]
  split_ifs
  · rw [mapWithCosts_constant]
    simp [Nat.mul_comm]
  · omega

def countedNumberedLive (T K t : ℕ) : List (Fin ((T+1)*(K+1)))×ℕ :=
  let histories:=countedShortHistoryList t
  let expanded:=countedFlatMap (countedHistoryKeys T K) histories.1
  let sorted:=countedUniqueSort expanded.1
  (sorted.1,histories.2+expanded.2+sorted.2)

theorem countedExpandedLive_value (T K t : ℕ) :
    (countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList t).1).1=
      (shortLiveList T K t).map (numberedExpertEquiv T K) := by
  rw [countedFlatMap_value,countedShortHistoryList_value]
  simp only [shortLiveList,List.map_flatMap]
  congr 1
  funext i
  simp only [countedHistoryKeys]
  split_ifs <;> simp [mapWithCosts_values,List.map_map,Function.comp_def]

set_option maxHeartbeats 1600000 in
theorem countedNumberedLive_value (T K t : ℕ) :
    (countedNumberedLive T K t).1=
      ((shortLiveExperts T K t).map (numberedExpertEquiv T K).toEmbedding).sort (·≤·) := by
  change (countedUniqueSort _).1=_
  rw [countedUniqueSort_value,countedExpandedLive_value]
  congr 1
  ext e
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_map,mem_shortLiveList,shortLiveExperts_eq]
  rfl

def shortMetadataBound (h K : ℕ) : ℕ :=
  5*h*(h+4)+5*h*(h*(h+6)+3)+2*(5*h)^2+
  5*h*(3*(K+1)+3)+2*(5*h*(K+1))^2

theorem countedNumberedLive_cost (T K t : ℕ) :
    (countedNumberedLive T K t).2≤shortMetadataBound (Nat.log 2 t+1) K := by
  have hh:=countedShortHistoryList_cost t
  have hl : (countedShortHistoryList t).1.length≤5*(Nat.log 2 t+1) := by
    rw [countedShortHistoryList_value,Finset.length_sort,shortActiveHistories_eq]
    exact activeHistories_card t
  have he:=countedFlatMap_cost (countedHistoryKeys T K) (countedShortHistoryList t).1
    (2*(K+1)+3) (K+1) (fun i _=>countedHistoryKeys_cost T K i)
      (fun i _=>countedHistoryKeys_length T K i)
  have he':=(he.trans (Nat.mul_le_mul_right _ hl))
  have hlen : (countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList t).1).1.length≤
      5*(Nat.log 2 t+1)*(K+1) := by
    rw [countedExpandedLive_value,List.length_map]
    exact shortLiveList_length T K t
  have hs:=countedUniqueSort_cost
    (countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList t).1).1
  have hm:=Nat.mul_self_le_mul_self hlen
  change (countedShortHistoryList t).2+
    (countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList t).1).2+
    (countedUniqueSort (countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList t).1).1).2≤_
  unfold shortMetadataBound
  nlinarith

def countedStandardLive (T K t : ℕ) := countedNumberedLive T K (min t T+1)

theorem countedStandardLive_value (T K t : ℕ) :
    (countedStandardLive T K t).1=((standardRationalSchedule T K).live t).sort (·≤·) :=
  countedNumberedLive_value T K _

theorem countedStandardLive_cost (T K t : ℕ) :
    (countedStandardLive T K t).2≤shortMetadataBound (Nat.log 2 (min t T+1)+1) K :=
  countedNumberedLive_cost T K _

end Paper254
#print axioms Paper254.countedStandardLive_value
#print axioms Paper254.countedStandardLive_cost
