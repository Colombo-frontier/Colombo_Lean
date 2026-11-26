import RationalPredictionCost254
import StandardMasterPrecision254

open scoped BigOperators
namespace Paper254

structure CountedRationalRoundData (d n : ℕ) where
  prediction : Fin d→ℚ
  gradient : Fin d→ℚ
  histories : List (Fin n×RationalHistoryData d)
  weights : List (Fin n×ℚ)

def countedHistoryBatch {d n : ℕ} (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (S : RationalSparseData d n) (lam : ℚ) (g w : Fin d→ℚ) :=
  mapWithCosts (fun e=>
    let out:=countedHistoryStep roundCost projectionCost oracle (cfg e) (S.histories e) lam g w
    ((e,out.1),out.2)) (live.sort (·≤·))

theorem countedHistoryBatch_cost {d n : ℕ} (hd : 0<d) (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (S : RationalSparseData d n) (lam : ℚ) (g w : Fin d→ℚ)
    (C : ℕ) (hcfg : ∀ e,historyStepCostBound d roundCost projectionCost (cfg e)≤C) :
    (countedHistoryBatch roundCost projectionCost oracle cfg live S lam g w).2≤live.card*C := by
  apply (mapWithCosts_bound _ _ C ?_).trans_eq
  · rw [Finset.length_sort]
  · intro e he
    exact (countedHistoryStep_cost hd roundCost projectionCost oracle (cfg e) (S.histories e) lam g w).trans (hcfg e)

/-- Prediction, the single gradient query, exponent computation, history
updates, and both master normalizers are shared within the round. -/
def countedRationalRound {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d) : CountedRationalRoundData d n×ℕ :=
  let prediction:=countedSparsePrediction live S
  let g:=Vector.ofFn (query prediction.1)
  let exponents:=countedSparseExponents live lam S (fun j=>g.get j) prediction.1
  let histories:=countedHistoryBatch roundCost projectionCost oracle cfg live S lam (fun j=>g.get j) prediction.1
  let weights:=countedMasterUpdate p roundCost live next S.weights (rationalLookup exponents.1) prior alpha
  (⟨prediction.1,fun j=>g.get j,histories.1,weights.1⟩,
    prediction.2+gradientCost+exponents.2+histories.2+weights.2)

theorem countedRationalRound_prediction {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d)
    (hsupport : ∀ e,e∉live → S.weights e=0) :
    (countedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam S query).1.prediction=
      rationalSparsePrediction S := countedSparsePrediction_value live S hsupport

theorem countedRationalRound_weights {d n : ℕ} (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d)
    (hsupport : ∀ e,e∉live → S.weights e=0) :
    rationalLookup (countedRationalRound p roundCost projectionCost gradientCost oracle cfg
      live next prior alpha lam S query).1.weights=
      (rationalSparseStep oracle cfg p lam live next prior alpha S
        (query (rationalSparsePrediction S))).weights := by
  simp only [countedRationalRound,countedSparsePrediction_value live S hsupport]
  have hg : (fun j=>(Vector.ofFn (query (rationalSparsePrediction S))).get j)=
      query (rationalSparsePrediction S) := by funext j; simp [Vector.get]
  rw [hg,countedMasterUpdate_value _ _ _ _ _ _ _ _ hsupport]
  exact rationalMasterUpdate_congr_live p live next S.weights _ _ prior alpha hsupport
    (fun e he=>countedSparseExponents_value live lam S _ e he)

theorem countedRationalRound_histories {d n : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (hspec : RationalProjectionSpec W oracle) (cfg : Fin n→RationalHistoryParameters)
    (lo : Fin n→ℝ) (hi : ℝ) (hlo : ∀ e,0<lo e) (hhi : 0<hi)
    (hguard : ∀ e,UniformHistoryGuards d (cfg e) (lo e) hi)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (hS : RationalSparseInvariant W lo hi live S)
    (query : RationalGradientQuery d) :
    (countedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam S query).1.histories=
      (live.sort (·≤·)).map (fun e=>(e,rationalHistoryStep oracle (cfg e) (S.histories e) lam
        (query (rationalSparsePrediction S)) (rationalSparsePrediction S))) := by
  simp only [countedRationalRound,countedSparsePrediction_value live S hS.support,countedHistoryBatch,
    mapWithCosts_values]
  have hg : (fun j=>(Vector.ofFn (query (rationalSparsePrediction S))).get j)=
      query (rationalSparsePrediction S) := by funext j; simp [Vector.get]
  rw [hg]
  apply List.map_congr_left
  intro e he
  exact congrArg (fun z=>(e,z)) (countedHistoryStep_value hd W roundCost projectionCost oracle hspec
    (cfg e) (lo e) hi (hlo e) hhi (hguard e) (S.histories e) (hS.histories e) lam _ _)

theorem countedRationalRound_cost {d n : ℕ} (hd : 0<d) (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d)
    (C : ℕ) (hcfg : ∀ e,historyStepCostBound d roundCost projectionCost (cfg e)≤C) :
    (countedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam S query).2≤
      live.card*(C+5*d+3*p+roundCost+32)+next.card*(3*p+roundCost+33)+2*p+4+gradientCost := by
  have hh:=countedHistoryBatch_cost hd roundCost projectionCost oracle cfg live S lam
    (fun j=>(Vector.ofFn (query (countedSparsePrediction live S).1)).get j)
    (countedSparsePrediction live S).1 C hcfg
  simp only [countedRationalRound,countedSparsePrediction_cost,countedSparseExponents_cost,countedMasterUpdate_cost]
  nlinarith

end Paper254
#print axioms Paper254.countedRationalRound_weights
#print axioms Paper254.countedRationalRound_histories
#print axioms Paper254.countedRationalRound_cost
