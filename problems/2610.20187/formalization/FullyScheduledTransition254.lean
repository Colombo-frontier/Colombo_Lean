import IntegerMetadata254

open scoped BigOperators
namespace Paper254

def fullyScheduledMaterializedStep {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    MaterializedRationalSparseData d ((T+1)*(K+1))×ℕ :=
  let live:=fullyCountedStandardLive T K t
  let next:=fullyCountedStandardLive T K (t+1)
  let updated:=list_keyedMaterializedStep S p roundCost projectionCost gradientCost oracle cfg
    live.1 next.1 prior alpha lam initial query
  (updated.1,live.2+next.2+updated.2)

theorem fullyScheduledMaterializedStep_program {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (fullyScheduledMaterializedStep T K t S p roundCost projectionCost gradientCost oracle cfg prior alpha lam initial query).1=
      S.step p roundCost projectionCost gradientCost oracle cfg
        ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
        (fun e=>(prior e).1) alpha lam initial query := by
  simp only [fullyScheduledMaterializedStep,fullyCountedStandardLive_program,list_keyedMaterializedStep_program,
    keyedMaterializedStep_program]

def fullMetadataRoundBound (T K d P : ℕ) := metadataRoundBound T K d P+6*Nat.log 2 (T+1)+8

theorem fullyScheduledMaterializedStep_metadata {d : ℕ} (T K t : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) (P : ℕ)
    (hp : ∀ e,(prior e).2≤P) (hH : S.histories.length≤standardLiveCap T K)
    (hW : S.weights.length≤standardLiveCap T K) :
    (fullyScheduledMaterializedStep T K t S p roundCost projectionCost gradientCost oracle cfg prior alpha lam initial query).2≤
      fullMetadataRoundBound T K d P := by
  have hs:=scheduledMaterializedStep_metadata T K t S p roundCost projectionCost gradientCost oracle cfg
    prior alpha lam initial query P hp hH hW
  have hc (j : ℕ) : (fullyCountedStandardLive T K j).2=
      (countedStandardLive T K j).2+3*Nat.log 2 (min j T+1)+4 := by
    simp only [fullyCountedStandardLive,countedLogTwo_spec,depth_countedNumberedLive_program,countedStandardLive]
    omega
  have hl (j : ℕ) : Nat.log 2 (min j T+1)≤Nat.log 2 (T+1) := Nat.log_mono_right (by omega)
  simp only [fullyScheduledMaterializedStep,fullyCountedStandardLive_program,list_keyedMaterializedStep_program,hc]
  simp only [scheduledMaterializedStep,countedStandardLive_value,list_keyedMaterializedStep_program] at hs
  dsimp only [fullMetadataRoundBound]
  have hl1:=hl t
  have hl2:=hl (t+1)
  omega

/-- Decoding the birth index uses one integer quotient and one comparison;
the common rational prior mass is supplied once for the entire round. -/
def cachedPriorWithCost (T K : ℕ) (i : Fin (T+1)) (rho : ℚ) (e : Fin ((T+1)*(K+1))) : ℚ×ℕ :=
  let birth:=e.val/(K+1)
  (if birth=i.val then rho else 0,2)

theorem cachedPriorWithCost_value (T K : ℕ) (i : Fin (T+1)) (e : Fin ((T+1)*(K+1))) :
    (cachedPriorWithCost T K i (1/(K+1:ℚ)) e).1=numberedBirthPrior T K i e := by
  simp only [cachedPriorWithCost,numberedBirthPrior,numberedExpertEquiv,finProdFinEquiv]
  congr 1
  apply propext
  constructor
  · intro h; apply Fin.ext; exact h
  · intro h; exact congrArg Fin.val h

theorem cachedPriorWithCost_cost (T K : ℕ) (i : Fin (T+1)) (rho : ℚ) (e : Fin ((T+1)*(K+1))) :
    (cachedPriorWithCost T K i rho e).2=2 := rfl

theorem fullyScheduled_total_metadata {d : ℕ} (T K : ℕ)
    (S : ℕ→MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : ℕ→Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha : ℕ→ℚ) (lam : ℚ) (initial : RationalHistoryData d) (query : ℕ→RationalGradientQuery d) (P : ℕ)
    (hp : ∀ t e,(prior t e).2≤P) (hH : ∀ t,(S t).histories.length≤standardLiveCap T K)
    (hW : ∀ t,(S t).weights.length≤standardLiveCap T K) :
    (∑ t∈Finset.range T,(fullyScheduledMaterializedStep T K t (S t) p roundCost projectionCost gradientCost
      oracle cfg (prior t) (alpha t) lam initial (query t)).2)≤T*fullMetadataRoundBound T K d P := by
  calc _≤∑ _t∈Finset.range T,fullMetadataRoundBound T K d P := Finset.sum_le_sum (by
    intro t _
    exact fullyScheduledMaterializedStep_metadata T K t (S t) p roundCost projectionCost gradientCost
      oracle cfg (prior t) (alpha t) lam initial (query t) P (hp t) (hH t) (hW t))
       _=_ := by simp

end Paper254
#print axioms Paper254.fullyScheduledMaterializedStep_program
#print axioms Paper254.fullyScheduledMaterializedStep_metadata
#print axioms Paper254.cachedPriorWithCost_value
#print axioms Paper254.fullyScheduled_total_metadata
