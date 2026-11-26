import RationalParameterSetup254
import FullyScheduledTransition254

open scoped BigOperators
namespace Paper254

theorem mapWithKeyCosts_add_keys {α β : Type} (f : α→(β×ℕ)×ℕ) (xs : List α) (c : ℕ) :
    mapWithKeyCosts (fun x=>((f x).1,(f x).2+c)) xs=
      ((mapWithKeyCosts f xs).1,(mapWithKeyCosts f xs).2+c*xs.length) := by
  induction xs with
  | nil => simp [mapWithKeyCosts]
  | cons x xs ih => simp only [mapWithKeyCosts,ih,List.length_cons,Nat.mul_add,Nat.mul_one]; congr 1 <;> omega

/-- One remainder and one vector access per scale lookup. The vector is
prepared once; no numerical parameter construction occurs in this call. -/
def countedCfgLookup (T K : ℕ) (rows : Vector RationalHistoryParameters (K+1))
    (e : Fin ((T+1)*(K+1))) : RationalHistoryParameters×ℕ :=
  (rows.get ⟨e.val%(K+1),Nat.mod_lt _ (by omega)⟩,2)

def cachedCfgHistoryBatch {d : ℕ} (T K roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (rows : Vector RationalHistoryParameters (K+1))
    (live : List (Fin ((T+1)*(K+1))))
    (histories : Fin ((T+1)*(K+1))→RationalHistoryData d×ℕ) (lam : ℚ) (g w : Fin d→ℚ) :=
  mapWithKeyCosts (fun e=>
    let se:=histories e
    let cfg:=countedCfgLookup T K rows e
    let out:=countedHistoryStep roundCost projectionCost oracle cfg.1 se.1 lam g w
    (((e,out.1),out.2),se.2+cfg.2)) live

theorem cachedCfgHistoryBatch_program {d : ℕ} (T K roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (rows : Vector RationalHistoryParameters (K+1))
    (live : List (Fin ((T+1)*(K+1))))
    (histories : Fin ((T+1)*(K+1))→RationalHistoryData d×ℕ) (lam : ℚ) (g w : Fin d→ℚ) :
    cachedCfgHistoryBatch T K roundCost projectionCost oracle rows live histories lam g w=
      ((list_keyedHistoryBatch roundCost projectionCost oracle
        (fun e=>(countedCfgLookup T K rows e).1) live histories lam g w).1,
      (list_keyedHistoryBatch roundCost projectionCost oracle
        (fun e=>(countedCfgLookup T K rows e).1) live histories lam g w).2+2*live.length) := by
  unfold cachedCfgHistoryBatch list_keyedHistoryBatch
  have hh := mapWithKeyCosts_add_keys (fun e=>
    let se:=histories e
    let out:=countedHistoryStep roundCost projectionCost oracle (countedCfgLookup T K rows e).1 se.1 lam g w
    (((e,out.1),out.2),se.2)) live 2
  exact hh

def cachedCfgRationalRound {d : ℕ} (T K p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (rows : Vector RationalHistoryParameters (K+1))
    (live next : List (Fin ((T+1)*(K+1))))
    (prior : Fin ((T+1)*(K+1))→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin ((T+1)*(K+1))→RationalHistoryData d×ℕ)
    (weights : Fin ((T+1)*(K+1))→ℚ×ℕ) (query : RationalGradientQuery d) :=
  let prediction:=list_keyedSparsePrediction live histories weights
  let g:=Vector.ofFn (query prediction.1.1)
  let exponents:=list_keyedSparseExponents live lam histories (fun j=>g.get j) prediction.1.1
  let updated:=cachedCfgHistoryBatch T K roundCost projectionCost oracle rows live histories lam
    (fun j=>g.get j) prediction.1.1
  let master:=list_keyedMasterUpdate p roundCost live next weights
    (countedKeyedLookup 0 exponents.1.1) prior alpha
  (((⟨prediction.1.1,fun j=>g.get j,updated.1.1,master.1.1⟩ : CountedRationalRoundData d ((T+1)*(K+1))),
    prediction.1.2+gradientCost+exponents.1.2+updated.1.2+master.1.2),
    prediction.2+exponents.2+updated.2+master.2)

theorem cachedCfgRationalRound_program {d : ℕ} (T K p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (rows : Vector RationalHistoryParameters (K+1))
    (live next : List (Fin ((T+1)*(K+1))))
    (prior : Fin ((T+1)*(K+1))→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin ((T+1)*(K+1))→RationalHistoryData d×ℕ)
    (weights : Fin ((T+1)*(K+1))→ℚ×ℕ) (query : RationalGradientQuery d) :
    cachedCfgRationalRound T K p roundCost projectionCost gradientCost oracle rows live next prior alpha lam histories weights query=
      ((list_keyedRationalRound p roundCost projectionCost gradientCost oracle
        (fun e=>(countedCfgLookup T K rows e).1) live next prior alpha lam histories weights query).1,
      (list_keyedRationalRound p roundCost projectionCost gradientCost oracle
        (fun e=>(countedCfgLookup T K rows e).1) live next prior alpha lam histories weights query).2+2*live.length) := by
  simp only [cachedCfgRationalRound,cachedCfgHistoryBatch_program,list_keyedRationalRound]
  congr 1 <;> omega

/-- Both key lists, the share scalar, and all configurations are cached.
The result records rational work separately from integer metadata work. -/
def cachedScheduledStep {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (rows : Vector RationalHistoryParameters (K+1)) (rho lam : ℚ)
    (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (MaterializedRationalSparseData d ((T+1)*(K+1))×ℕ)×ℕ :=
  let live:=fullyCountedStandardLive T K t
  let next:=fullyCountedStandardLive T K (t+1)
  let alpha : ℚ×ℕ := (1/(t+2:ℚ),1)
  let prior:=cachedPriorWithCost T K ⟨min (t+1) T,by omega⟩ rho
  let out:=cachedCfgRationalRound T K p roundCost projectionCost gradientCost oracle rows
    live.1 next.1 prior alpha.1 lam (list_countedGuardedLookup initial S.histories live.1)
    (list_countedGuardedLookup 0 S.weights live.1) query
  let pruned:=mapWithCosts (fun e=>let found:=countedKeyedLookup initial out.1.1.histories e
    ((e,found.1),found.2)) next.1
  ((⟨pruned.1,out.1.1.weights⟩,out.1.2+alpha.2),live.2+next.2+out.2+pruned.2+6)

set_option maxHeartbeats 1200000 in
theorem cachedScheduledStep_program {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (rows : Vector RationalHistoryParameters (K+1)) (lam : ℚ)
    (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (cachedScheduledStep T K t S p roundCost projectionCost gradientCost oracle rows (1/(K+1:ℚ)) lam initial query).1.1=
      S.step p roundCost projectionCost gradientCost oracle (fun e=>(countedCfgLookup T K rows e).1)
        ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
        ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) lam initial query := by
  have hh:=fullyScheduledMaterializedStep_program T K t S p roundCost projectionCost gradientCost oracle
    (fun e=>(countedCfgLookup T K rows e).1)
    (cachedPriorWithCost T K ⟨min (t+1) T,by omega⟩ (1/(K+1:ℚ))) (1/(t+2:ℚ)) lam initial query
  simp only [cachedPriorWithCost_value] at hh
  simpa only [cachedScheduledStep,cachedCfgRationalRound_program,fullyScheduledMaterializedStep,
    list_keyedMaterializedStep] using hh

def cachedMetadataRoundBound (T K d : ℕ) := fullMetadataRoundBound T K d 2+2*standardLiveCap T K+6

theorem cachedScheduledStep_metadata {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (rows : Vector RationalHistoryParameters (K+1)) (rho lam : ℚ)
    (initial : RationalHistoryData d) (query : RationalGradientQuery d)
    (hH : S.histories.length≤standardLiveCap T K) (hW : S.weights.length≤standardLiveCap T K) :
    (cachedScheduledStep T K t S p roundCost projectionCost gradientCost oracle rows rho lam initial query).2≤
      cachedMetadataRoundBound T K d := by
  have hh:=fullyScheduledMaterializedStep_metadata T K t S p roundCost projectionCost gradientCost oracle
    (fun e=>(countedCfgLookup T K rows e).1) (cachedPriorWithCost T K ⟨min (t+1) T,by omega⟩ rho)
    (1/(t+2:ℚ)) lam initial query 2 (fun _=>le_rfl) hH hW
  have hl : (fullyCountedStandardLive T K t).1.length≤standardLiveCap T K := by
    rw [fullyCountedStandardLive_program,Finset.length_sort]
    exact standardRationalSchedule_uniform_card T K t
  simp only [cachedScheduledStep,cachedCfgRationalRound_program,cachedMetadataRoundBound,
    fullyScheduledMaterializedStep,list_keyedMaterializedStep] at *
  omega


theorem list_keyedRationalRound_as_keyed {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ×ℕ) (alpha lam : ℚ)
    (histories : Fin n→RationalHistoryData d×ℕ) (weights : Fin n→ℚ×ℕ)
    (query : RationalGradientQuery d) :
    list_keyedRationalRound p roundCost projectionCost gradientCost oracle cfg
      (live.sort (·≤·)) (next.sort (·≤·)) prior alpha lam histories weights query=
    keyedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam histories weights query := rfl

theorem list_countedGuardedLookup_as_keyed {n : ℕ} {α : Type} (fallback : α)
    (entries : List (Fin n×α)) (live : Finset (Fin n)) :
    list_countedGuardedLookup fallback entries (live.sort (·≤·))=countedGuardedLookup fallback entries live := rfl

set_option maxHeartbeats 1200000 in
theorem cachedScheduledStep_rational {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (rows : Vector RationalHistoryParameters (K+1)) (lam : ℚ)
    (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (cachedScheduledStep T K t S p roundCost projectionCost gradientCost oracle rows (1/(K+1:ℚ)) lam initial query).1.2=
      (countedRationalRound p roundCost projectionCost gradientCost oracle (fun e=>(countedCfgLookup T K rows e).1)
        ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
        ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) lam
        ((S.compactView ((standardRationalSchedule T K).live t) initial).ambient initial) query).2+1 := by
  simp only [cachedScheduledStep,cachedCfgRationalRound_program,fullyCountedStandardLive_program,
    list_keyedRationalRound_as_keyed,list_countedGuardedLookup_as_keyed,keyedRationalRound_program,
    countedGuardedLookup_value,keyedLookup_rational,cachedPriorWithCost_value,
    MaterializedRationalSparseData.compactView,CompactRationalSparseData.ambient,
    CompactRationalSparseData.weightView]
  rfl

end Paper254
#print axioms Paper254.cachedCfgRationalRound_program
#print axioms Paper254.cachedScheduledStep_program
#print axioms Paper254.cachedScheduledStep_metadata
#print axioms Paper254.cachedScheduledStep_rational
