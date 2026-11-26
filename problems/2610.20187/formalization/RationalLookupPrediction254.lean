import RationalLookupRound254

open scoped BigOperators
namespace Paper254

def keyedSparsePrediction {d n : ℕ} (live : Finset (Fin n))
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ) :
    ((Fin d→ℚ)×ℕ)×ℕ :=
  let rows:=Vector.ofFn (fun j:Fin d=>
    let inputs:=mapWithKeyCosts (fun e=>
      let we:=weights e; let se:=histories e
      (((we.1,se.1.mean j),0),we.2+se.2)) (live.sort (·≤·))
    (countedDot inputs.1.1,inputs.2))
  ((fun j=>(rows.get j).1.1,(rows.toList.map (fun r=>r.1.2)).sum),
    (rows.toList.map Prod.snd).sum)

theorem keyedSparsePrediction_program {d n : ℕ} (live : Finset (Fin n))
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ) :
    (keyedSparsePrediction live histories weights).1=
      countedSparsePrediction live ⟨fun e=>(histories e).1,fun e=>(weights e).1⟩ := by
  simp only [keyedSparsePrediction,mapWithKeyCosts_program,mapWithCosts_values,countedSparsePrediction]
  simp [Vector.get,Vector.toList_ofFn,List.map_ofFn]
  rfl

theorem keyedSparsePrediction_keys {d n : ℕ} (live : Finset (Fin n))
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ) (H W : ℕ)
    (hh : ∀ e∈live,(histories e).2≤H) (hw : ∀ e∈live,(weights e).2≤W) :
    (keyedSparsePrediction live histories weights).2≤d*live.card*(W+H) := by
  have hr (j : Fin d) :
      (mapWithKeyCosts (fun e=>
        let we:=weights e; let se:=histories e
        (((we.1,se.1.mean j),0),we.2+se.2)) (live.sort (·≤·))).2≤live.card*(W+H) := by
    apply (mapWithKeyCosts_keys _ _ (W+H) ?_).trans_eq
    · rw [Finset.length_sort]
    · intro e he
      exact Nat.add_le_add (hw e (by simpa using he)) (hh e (by simpa using he))
  simp only [keyedSparsePrediction,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  calc _≤∑ _j : Fin d,live.card*(W+H) := Finset.sum_le_sum (by intro j _; exact hr j)
       _=d*live.card*(W+H) := by simp [Nat.mul_assoc]

def keyedSparseExponents {d n : ℕ} (live : Finset (Fin n)) (lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (g w : Fin d→ℚ) :
    (List (Fin n×ℚ)×ℕ)×ℕ :=
  mapWithKeyCosts (fun e=>
    let se:=histories e
    let q:=countedSurrogateExponent lam g w se.1.mean
    (((e,q.1),q.2),se.2)) (live.sort (·≤·))

theorem keyedSparseExponents_program {d n : ℕ} (live : Finset (Fin n)) (lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ) (g w : Fin d→ℚ) :
    (keyedSparseExponents live lam histories g w).1=
      countedSparseExponents live lam ⟨fun e=>(histories e).1,weights⟩ g w := by
  simp only [keyedSparseExponents,mapWithKeyCosts_program,countedSparseExponents]

theorem keyedSparseExponents_keys {d n : ℕ} (live : Finset (Fin n)) (lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (g w : Fin d→ℚ) (H : ℕ)
    (hh : ∀ e∈live,(histories e).2≤H) :
    (keyedSparseExponents live lam histories g w).2≤live.card*H := by
  apply (mapWithKeyCosts_keys _ _ H ?_).trans_eq
  · rw [Finset.length_sort]
  · intro e he; exact hh e (by simpa using he)

def keyedHistoryBatch {d n : ℕ} (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (histories : Fin n→RationalHistoryData d×ℕ) (lam : ℚ) (g w : Fin d→ℚ) :=
  mapWithKeyCosts (fun e=>
    let se:=histories e
    let out:=countedHistoryStep roundCost projectionCost oracle (cfg e) se.1 lam g w
    (((e,out.1),out.2),se.2)) (live.sort (·≤·))

theorem keyedHistoryBatch_program {d n : ℕ} (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ)
    (lam : ℚ) (g w : Fin d→ℚ) :
    (keyedHistoryBatch roundCost projectionCost oracle cfg live histories lam g w).1=
      countedHistoryBatch roundCost projectionCost oracle cfg live ⟨fun e=>(histories e).1,weights⟩ lam g w := by
  simp only [keyedHistoryBatch,mapWithKeyCosts_program,countedHistoryBatch]

theorem keyedHistoryBatch_keys {d n : ℕ} (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (histories : Fin n→RationalHistoryData d×ℕ) (lam : ℚ) (g w : Fin d→ℚ)
    (H : ℕ) (hh : ∀ e∈live,(histories e).2≤H) :
    (keyedHistoryBatch roundCost projectionCost oracle cfg live histories lam g w).2≤live.card*H := by
  apply (mapWithKeyCosts_keys _ _ H ?_).trans_eq
  · rw [Finset.length_sort]
  · intro e he; exact hh e (by simpa using he)

end Paper254
#print axioms Paper254.keyedSparsePrediction_program
#print axioms Paper254.keyedSparsePrediction_keys
#print axioms Paper254.keyedHistoryBatch_program
