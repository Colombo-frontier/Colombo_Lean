import EfficientHistoryCost254

open scoped BigOperators
namespace Paper254

def mapWithCosts {α β : Type} (f : α→β×ℕ) : List α→List β×ℕ
  | []=>([],0)
  | x::xs=>let head:=f x; let tail:=mapWithCosts f xs
           (head.1::tail.1,head.2+tail.2)

theorem mapWithCosts_values {α β : Type} (f : α→β×ℕ) (xs : List α) :
    (mapWithCosts f xs).1=xs.map (fun x=>(f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mapWithCosts,List.map_cons,ih]

theorem mapWithCosts_bound {α β : Type} (f : α→β×ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs,(f x).2≤C) : (mapWithCosts f xs).2≤xs.length*C := by
  induction xs with
  | nil => simp [mapWithCosts]
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [mapWithCosts,List.length_cons]
    nlinarith

def visitCountedHistories {d : ℕ} (T K t roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : HistoryExpert T K→RationalHistoryParameters)
    (S : HistoryExpert T K→RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :=
  mapWithCosts (fun e=>
    let next:=countedHistoryStep roundCost projectionCost oracle (cfg e) (S e) lam g w
    ((e,next.1),next.2)) (shortLiveList T K t)

theorem visitCountedHistories_cost {d : ℕ} (hd : 0<d)
    (T K t roundCost projectionCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : HistoryExpert T K→RationalHistoryParameters)
    (S : HistoryExpert T K→RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ)
    (C : ℕ) (hcfg : ∀ e,historyStepCostBound d roundCost projectionCost (cfg e)≤C) :
    (visitCountedHistories T K t roundCost projectionCost oracle cfg S lam g w).2≤
      (shortLiveList T K t).length*C := by
  apply mapWithCosts_bound
  intro e he
  exact (countedHistoryStep_cost hd roundCost projectionCost oracle (cfg e) (S e) lam g w).trans (hcfg e)

theorem visitCountedHistories_values {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (T K t roundCost projectionCost : ℕ) (oracle : RationalProjectionProcedure d)
    (hspec : RationalProjectionSpec W oracle) (cfg : HistoryExpert T K→RationalHistoryParameters)
    (lo : HistoryExpert T K→ℝ) (hi : ℝ) (hlo : ∀ e,0<lo e) (hhi : 0<hi)
    (hguard : ∀ e,UniformHistoryGuards d (cfg e) (lo e) hi)
    (S : HistoryExpert T K→RationalHistoryData d)
    (hS : ∀ e∈liveExperts T K t,RationalHistoryInvariant W (lo e) hi (S e))
    (lam : ℚ) (g w : Fin d→ℚ) :
    (visitCountedHistories T K t roundCost projectionCost oracle cfg S lam g w).1=
      (shortLiveList T K t).map (fun e=>(e,rationalHistoryStep oracle (cfg e) (S e) lam g w)) := by
  rw [visitCountedHistories,mapWithCosts_values]
  apply List.map_congr_left
  intro e he
  have hh:=countedHistoryStep_value hd W roundCost projectionCost oracle hspec (cfg e)
    (lo e) hi (hlo e) hhi (hguard e) (S e) (hS e ((mem_shortLiveList T K t e).mp he)) lam g w
  exact congrArg (fun z=>(e,z)) hh

/-- Total charge of the actual history-update traversal. The states and
queries may depend on all earlier computed predictions. -/
theorem sparseHistory_total_cost {d : ℕ} (hd : 0<d) (T roundCost projectionCost : ℕ)
    (hT : 0<T) (oracle : RationalProjectionProcedure d)
    (cfg : HistoryExpert T (scaleCount T)→RationalHistoryParameters)
    (states : ℕ→HistoryExpert T (scaleCount T)→RationalHistoryData d)
    (lam : ℚ) (grad prediction : ℕ→Fin d→ℚ) (C : ℕ)
    (hcfg : ∀ e,historyStepCostBound d roundCost projectionCost (cfg e)≤C) :
    (∑ t∈Finset.range T,
      ((visitCountedHistories T (scaleCount T) (t+1) roundCost projectionCost oracle cfg
        (states t) lam (grad t) (prediction t)).2:ℝ))≤20*T*logFactor T^2*C := by
  have hb : (∑ t∈Finset.range T,
      (visitCountedHistories T (scaleCount T) (t+1) roundCost projectionCost oracle cfg
        (states t) lam (grad t) (prediction t)).2)≤totalHistoryCalls T*C := by
    calc
      _≤∑ t∈Finset.range T,(shortLiveList T (scaleCount T) (t+1)).length*C :=
        Finset.sum_le_sum (fun t ht=>visitCountedHistories_cost hd T (scaleCount T) (t+1)
          roundCost projectionCost oracle cfg (states t) lam (grad t) (prediction t) C hcfg)
      _=totalHistoryCalls T*C := by rw [←Finset.sum_mul]; rfl
  have hr : (∑ t∈Finset.range T,
      ((visitCountedHistories T (scaleCount T) (t+1) roundCost projectionCost oracle cfg
        (states t) lam (grad t) (prediction t)).2:ℝ))≤(totalHistoryCalls T:ℝ)*C := by
    exact_mod_cast hb
  exact hr.trans (history_oracle_cost_composition T hT C (by positivity))

end Paper254
#print axioms Paper254.visitCountedHistories_values
#print axioms Paper254.sparseHistory_total_cost
