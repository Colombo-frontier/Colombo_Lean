import RationalLookupTransition254

namespace Paper254

def list_keyedLiveSoftmax {n : ℕ} (p roundCost : ℕ) (live : List (Fin n))
    (w z : Fin n→ℚ×ℕ) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let raw:=mapWithKeyCosts (fun e=>
    let we:=w e; let ze:=z e
    let exponential:=countedRationalExp ze.1 (p+4)
    (((e,we.1*exponential.1),exponential.2+1),we.2+ze.2)) live
  let normalized:=countedNormalize raw.1.1
  let power:=countedRatPow 2 p
  let bump : ℚ×ℕ :=(3/(2*power.1),2)
  let upper:=mapWithCosts (fun e=>((e.1,dyadicCeil (p+1) e.2+bump.1),roundCost+1)) normalized.1
  let out:=countedNormalize upper.1
  ((out.1,raw.1.2+normalized.2+power.2+bump.2+upper.2+out.2),raw.2)

def list_keyedPruneShare {n : ℕ} (w prior : Fin n→ℚ×ℕ) (alpha : ℚ) (next : List (Fin n)) :
    (List (Fin n×ℚ)×ℕ)×ℕ :=
  let raw:=mapWithKeyCosts (fun e=>
    let we:=w e; let pe:=prior e
    (((e,(1-alpha)*we.1+alpha*pe.1),4),we.2+pe.2)) next
  let out:=countedNormalize raw.1.1
  ((out.1,raw.1.2+out.2),raw.2)

def list_keyedMasterUpdate {n : ℕ} (p roundCost : ℕ) (live next : List (Fin n))
    (w z prior : Fin n→ℚ×ℕ) (alpha : ℚ) : (List (Fin n×ℚ)×ℕ)×ℕ :=
  let weighted:=list_keyedLiveSoftmax p roundCost live w z
  let shared:=list_keyedPruneShare (countedKeyedLookup 0 weighted.1.1) prior alpha next
  let out:=list_keyedLiveSoftmax p roundCost next (countedKeyedLookup 0 shared.1.1) (fun _=>(0,0))
  ((out.1.1,weighted.1.2+shared.1.2+out.1.2),weighted.2+shared.2+out.2)

def list_keyedSparsePrediction {d n : ℕ} (live : List (Fin n))
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ) :
    ((Fin d→ℚ)×ℕ)×ℕ :=
  let rows:=Vector.ofFn (fun j:Fin d=>
    let inputs:=mapWithKeyCosts (fun e=>
      let we:=weights e; let se:=histories e
      (((we.1,se.1.mean j),0),we.2+se.2)) live
    (countedDot inputs.1.1,inputs.2))
  ((fun j=>(rows.get j).1.1,(rows.toList.map (fun r=>r.1.2)).sum),
    (rows.toList.map Prod.snd).sum)

def list_keyedSparseExponents {d n : ℕ} (live : List (Fin n)) (lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (g w : Fin d→ℚ) :
    (List (Fin n×ℚ)×ℕ)×ℕ :=
  mapWithKeyCosts (fun e=>
    let se:=histories e
    let q:=countedSurrogateExponent lam g w se.1.mean
    (((e,q.1),q.2),se.2)) live

def list_keyedHistoryBatch {d n : ℕ} (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : List (Fin n)) (histories : Fin n→RationalHistoryData d×ℕ) (lam : ℚ) (g w : Fin d→ℚ) :=
  mapWithKeyCosts (fun e=>
    let se:=histories e
    let out:=countedHistoryStep roundCost projectionCost oracle (cfg e) se.1 lam g w
    (((e,out.1),out.2),se.2)) live

def list_keyedRationalRound {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : List (Fin n)) (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ)
    (query : RationalGradientQuery d) : (CountedRationalRoundData d n×ℕ)×ℕ :=
  let prediction:=list_keyedSparsePrediction live histories weights
  let g:=Vector.ofFn (query prediction.1.1)
  let exponents:=list_keyedSparseExponents live lam histories (fun j=>g.get j) prediction.1.1
  let updated:=list_keyedHistoryBatch roundCost projectionCost oracle cfg live histories lam
    (fun j=>g.get j) prediction.1.1
  let master:=list_keyedMasterUpdate p roundCost live next weights
    (countedKeyedLookup 0 exponents.1.1) prior alpha
  ((⟨prediction.1.1,fun j=>g.get j,updated.1.1,master.1.1⟩,
    prediction.1.2+gradientCost+exponents.1.2+updated.1.2+master.1.2),
    prediction.2+exponents.2+updated.2+master.2)

def list_countedGuardedLookup {n : ℕ} {α : Type} (fallback : α) (entries : List (Fin n×α))
    (live : List (Fin n)) (e : Fin n) : α×ℕ :=
  let found:=countedContains e live
  if found.1=true then
    let item:=countedKeyedLookup fallback entries e
    (item.1,found.2+item.2)
  else (fallback,found.2)

def list_keyedMaterializedStep {d n : ℕ} (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (live next : List (Fin n))
    (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ) (initial : RationalHistoryData d)
    (query : RationalGradientQuery d) : MaterializedRationalSparseData d n×ℕ :=
  let out:=list_keyedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam
    (list_countedGuardedLookup initial S.histories live) (list_countedGuardedLookup 0 S.weights live) query
  let pruned:=mapWithCosts (fun e=>let found:=countedKeyedLookup initial out.1.1.histories e
    ((e,found.1),found.2)) next
  (⟨pruned.1,out.1.1.weights⟩,out.2+pruned.2)

theorem list_keyedMaterializedStep_program {d n : ℕ} (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (live next : Finset (Fin n))
    (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ) (initial : RationalHistoryData d)
    (query : RationalGradientQuery d) :
    list_keyedMaterializedStep S p roundCost projectionCost gradientCost oracle cfg
      (live.sort (·≤·)) (next.sort (·≤·)) prior alpha lam initial query=
      keyedMaterializedStep S p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam initial query := rfl

/-- Both short key lists are materialized once and shared by all component
loops, including guard checks and pruning. No component sorts or scans an
ambient set of all possible births. -/
def scheduledMaterializedStep {d : ℕ} (T K t : ℕ) (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    MaterializedRationalSparseData d ((T+1)*(K+1))×ℕ :=
  let live:=countedStandardLive T K t
  let next:=countedStandardLive T K (t+1)
  let updated:=list_keyedMaterializedStep S p roundCost projectionCost gradientCost oracle cfg
    live.1 next.1 prior alpha lam initial query
  (updated.1,live.2+next.2+updated.2)

theorem scheduledMaterializedStep_program {d : ℕ} (T K t : ℕ) (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (scheduledMaterializedStep T K t S p roundCost projectionCost gradientCost oracle cfg prior alpha lam initial query).1=
      S.step p roundCost projectionCost gradientCost oracle cfg
        ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
        (fun e=>(prior e).1) alpha lam initial query := by
  simp only [scheduledMaterializedStep,countedStandardLive_value,list_keyedMaterializedStep_program,
    keyedMaterializedStep_program]

def metadataRoundBound (T K d P : ℕ) : ℕ :=
  let N:=standardLiveCap T K
  2*shortMetadataBound (Nat.log 2 (T+1)+1) K+(4*d+10)*N^2+N*P

theorem shortMetadataBound_mono {h h' K : ℕ} (hh : h≤h') :
    shortMetadataBound h K≤shortMetadataBound h' K := by
  unfold shortMetadataBound
  gcongr

theorem scheduledMaterializedStep_metadata {d : ℕ} (T K t : ℕ) (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) (P : ℕ)
    (hp : ∀ e, (prior e).2≤P) (hH : S.histories.length≤standardLiveCap T K)
    (hW : S.weights.length≤standardLiveCap T K) :
    (scheduledMaterializedStep T K t S p roundCost projectionCost gradientCost oracle cfg prior alpha lam initial query).2≤
      metadataRoundBound T K d P := by
  have hsort (j : ℕ) : (countedStandardLive T K j).2≤shortMetadataBound (Nat.log 2 (T+1)+1) K := by
    apply (countedStandardLive_cost T K j).trans
    apply shortMetadataBound_mono
    exact Nat.add_le_add_right (Nat.log_mono_right (by omega : min j T+1≤T+1)) 1
  have hN:=standardRationalSchedule_uniform_card T K t
  have hM:=standardRationalSchedule_uniform_card T K (t+1)
  have hu:=keyedMaterializedStep_keys S p roundCost projectionCost gradientCost oracle cfg
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    prior alpha lam initial query P (fun e _=>hp e)
  have hpoly :
      d*((standardRationalSchedule T K).live t).card*
        (2*((standardRationalSchedule T K).live t).card+S.weights.length+S.histories.length)+
      2*((standardRationalSchedule T K).live t).card*
        (((standardRationalSchedule T K).live t).card+S.histories.length)+
      ((standardRationalSchedule T K).live t).card*(2*((standardRationalSchedule T K).live t).card+S.weights.length)+
      ((standardRationalSchedule T K).live (t+1)).card*(2*((standardRationalSchedule T K).live t).card+P)+
      ((standardRationalSchedule T K).live (t+1)).card^2≤
      (4*d+10)*(standardLiveCap T K)^2+standardLiveCap T K*P := by
    calc _≤d*(standardLiveCap T K)*(2*standardLiveCap T K+standardLiveCap T K+standardLiveCap T K)+
      2*standardLiveCap T K*(standardLiveCap T K+standardLiveCap T K)+
      standardLiveCap T K*(2*standardLiveCap T K+standardLiveCap T K)+
      standardLiveCap T K*(2*standardLiveCap T K+P)+(standardLiveCap T K)^2 := by gcongr
         _=_ := by ring
  have hf:=hu.trans hpoly
  simp only [scheduledMaterializedStep,countedStandardLive_value,list_keyedMaterializedStep_program]
  dsimp only [metadataRoundBound]
  have hs:=hsort t
  have hs':=hsort (t+1)
  omega

end Paper254
#print axioms Paper254.scheduledMaterializedStep_program
#print axioms Paper254.scheduledMaterializedStep_metadata
