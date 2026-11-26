import RationalLookupPrediction254

namespace Paper254

def keyedRationalRound {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ)
    (query : RationalGradientQuery d) : (CountedRationalRoundData d n×ℕ)×ℕ :=
  let prediction:=keyedSparsePrediction live histories weights
  let g:=Vector.ofFn (query prediction.1.1)
  let exponents:=keyedSparseExponents live lam histories (fun j=>g.get j) prediction.1.1
  let updated:=keyedHistoryBatch roundCost projectionCost oracle cfg live histories lam
    (fun j=>g.get j) prediction.1.1
  let master:=keyedMasterUpdate p roundCost live next weights
    (countedKeyedLookup 0 exponents.1.1) prior alpha
  ((⟨prediction.1.1,fun j=>g.get j,updated.1.1,master.1.1⟩,
    prediction.1.2+gradientCost+exponents.1.2+updated.1.2+master.1.2),
    prediction.2+exponents.2+updated.2+master.2)

theorem keyedRationalRound_program {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ)
    (query : RationalGradientQuery d) :
    (keyedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam
      histories weights query).1=countedRationalRound p roundCost projectionCost gradientCost oracle cfg
      live next (fun e=>(prior e).1) alpha lam ⟨fun e=>(histories e).1,fun e=>(weights e).1⟩ query := by
  simp only [keyedRationalRound,keyedSparsePrediction_program,
    keyedSparseExponents_program live lam histories (fun e=>(weights e).1),
    keyedHistoryBatch_program roundCost projectionCost oracle cfg live histories (fun e=>(weights e).1),
    keyedMasterUpdate_program,countedKeyedLookup_value,keyedLookup_rational,countedRationalRound]

theorem keyedRationalRound_keys {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ)
    (query : RationalGradientQuery d) (H W P : ℕ)
    (hh : ∀ e∈live,(histories e).2≤H) (hw : ∀ e∈live,(weights e).2≤W)
    (hp : ∀ e∈next,(prior e).2≤P) :
    (keyedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam
      histories weights query).2≤
      d*live.card*(W+H)+2*live.card*H+live.card*(W+live.card)+next.card*(live.card+P)+next.card^2 := by
  let prediction:=keyedSparsePrediction live histories weights
  let g:=fun j=>(Vector.ofFn (query prediction.1.1)).get j
  let exponents:=keyedSparseExponents live lam histories g prediction.1.1
  have hpred:=keyedSparsePrediction_keys live histories weights H W hh hw
  have hexp:=keyedSparseExponents_keys live lam histories g prediction.1.1 H hh
  have hhist:=keyedHistoryBatch_keys roundCost projectionCost oracle cfg live histories lam g prediction.1.1 H hh
  have hlen : exponents.1.1.length=live.card := by
    simp [exponents,keyedSparseExponents,mapWithKeyCosts_program,mapWithCosts_length]
  have hmaster:=keyedMasterUpdate_keys p roundCost live next weights
    (countedKeyedLookup 0 exponents.1.1) prior alpha W live.card P hw
    (by intro e _; simpa only [hlen] using (countedKeyedLookup_cost (0:ℚ) exponents.1.1 e)) hp
  change prediction.2+exponents.2+_+_≤_
  dsimp only [prediction,exponents,g] at hpred hexp hhist hmaster ⊢
  nlinarith

def countedGuardedLookup {n : ℕ} {α : Type} (fallback : α) (entries : List (Fin n×α))
    (live : Finset (Fin n)) (e : Fin n) : α×ℕ :=
  let found:=countedContains e (live.sort (·≤·))
  if found.1=true then
    let item:=countedKeyedLookup fallback entries e
    (item.1,found.2+item.2)
  else (fallback,found.2)

theorem countedGuardedLookup_value {n : ℕ} {α : Type} (fallback : α) (entries : List (Fin n×α))
    (live : Finset (Fin n)) (e : Fin n) :
    (countedGuardedLookup fallback entries live e).1=
      if e∈live then keyedLookup fallback entries e else fallback := by
  by_cases he : e∈live <;>
    simp [countedGuardedLookup,countedContains_value,countedKeyedLookup_value,he]

theorem countedGuardedLookup_keys {n : ℕ} {α : Type} (fallback : α) (entries : List (Fin n×α))
    (live : Finset (Fin n)) (e : Fin n) :
    (countedGuardedLookup fallback entries live e).2≤live.card+entries.length := by
  have hm:=countedContains_cost e (live.sort (·≤·))
  have hi:=countedKeyedLookup_cost fallback entries e
  simp only [Finset.length_sort] at hm
  dsimp only [countedGuardedLookup]
  split_ifs <;> simp only <;> omega

def keyedMaterializedStep {d n : ℕ} (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (live next : Finset (Fin n))
    (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ) (initial : RationalHistoryData d)
    (query : RationalGradientQuery d) : MaterializedRationalSparseData d n×ℕ :=
  let out:=keyedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam
    (countedGuardedLookup initial S.histories live) (countedGuardedLookup 0 S.weights live) query
  let pruned:=countedHistoryPrune initial out.1.1.histories next
  (⟨pruned.1,out.1.1.weights⟩,out.2+pruned.2)

theorem keyedMaterializedStep_program {d n : ℕ} (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (live next : Finset (Fin n))
    (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ) (initial : RationalHistoryData d)
    (query : RationalGradientQuery d) :
    (keyedMaterializedStep S p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam initial query).1=
      S.step p roundCost projectionCost gradientCost oracle cfg live next (fun e=>(prior e).1) alpha lam initial query := by
  simp only [keyedMaterializedStep,keyedRationalRound_program,countedHistoryPrune_value,
    countedGuardedLookup_value,keyedLookup_rational,MaterializedRationalSparseData.step,
    MaterializedRationalSparseData.compactView,CompactRationalSparseData.ambient,CompactRationalSparseData.weightView]
  rfl

theorem keyedMaterializedStep_keys {d n : ℕ} (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (live next : Finset (Fin n))
    (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ) (initial : RationalHistoryData d)
    (query : RationalGradientQuery d) (P : ℕ) (hp : ∀ e∈next,(prior e).2≤P) :
    (keyedMaterializedStep S p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam initial query).2≤
      d*live.card*(2*live.card+S.weights.length+S.histories.length)+
      2*live.card*(live.card+S.histories.length)+live.card*(2*live.card+S.weights.length)+
      next.card*(2*live.card+P)+next.card^2 := by
  have hout:=keyedRationalRound_keys p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam
    (countedGuardedLookup initial S.histories live) (countedGuardedLookup 0 S.weights live) query
    (live.card+S.histories.length) (live.card+S.weights.length) P
    (fun e _=>countedGuardedLookup_keys initial S.histories live e)
    (fun e _=>countedGuardedLookup_keys 0 S.weights live e) hp
  let out:=keyedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam
    (countedGuardedLookup initial S.histories live) (countedGuardedLookup 0 S.weights live) query
  have hlen : out.1.1.histories.length=live.card := by
    simp [out,keyedRationalRound,keyedHistoryBatch,mapWithKeyCosts_program,mapWithCosts_length]
  have hprune:=countedHistoryPrune_cost initial out.1.1.histories next
  rw [hlen] at hprune
  change out.2+_≤_
  nlinarith

end Paper254
#print axioms Paper254.keyedMaterializedStep_program
#print axioms Paper254.keyedMaterializedStep_keys
