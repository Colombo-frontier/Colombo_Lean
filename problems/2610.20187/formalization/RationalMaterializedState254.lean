import RationalCompactRun254
import RationalRoundCost254

open scoped BigOperators
namespace Paper254

def keyedLookup {n : ℕ} {α : Type*} (fallback : α) (entries : List (Fin n×α)) (j : Fin n) : α :=
  match entries with
  | [] => fallback
  | (i,x)::xs => if i=j then x else keyedLookup fallback xs j

theorem keyedLookup_map {n : ℕ} {α : Type*} (fallback : α) (xs : List (Fin n))
    (f : Fin n → α) (j : Fin n) :
    keyedLookup fallback (xs.map (fun i => (i,f i))) j=if j∈xs then f j else fallback := by
  induction xs with
  | nil => simp [keyedLookup]
  | cons i xs ih =>
    by_cases h : i=j
    · subst i; simp [keyedLookup]
    · simp [keyedLookup,h,ih,Ne.symm h]

structure MaterializedRationalSparseData (d n : ℕ) where
  histories : List (Fin n×RationalHistoryData d)
  weights : List (Fin n×ℚ)

namespace MaterializedRationalSparseData
variable {d n : ℕ}

def compactView (S : MaterializedRationalSparseData d n) (live : Finset (Fin n))
    (initial : RationalHistoryData d) : CompactRationalSparseData d n live where
  histories e := keyedLookup initial S.histories e.val
  weights e := rationalLookup S.weights e.val

def ofCompact {live : Finset (Fin n)} (S : CompactRationalSparseData d n live)
    (initial : RationalHistoryData d) : MaterializedRationalSparseData d n where
  histories := (live.sort (·≤·)).map (fun e => (e,(S.ambient initial).histories e))
  weights := (live.sort (·≤·)).map (fun e => (e,S.weightView e))

theorem compactView_ofCompact {live : Finset (Fin n)} (S : CompactRationalSparseData d n live)
    (initial : RationalHistoryData d) : (ofCompact S initial).compactView live initial=S := by
  apply CompactRationalSparseData.ext
  · intro e
    simp [compactView,ofCompact,keyedLookup_map,CompactRationalSparseData.ambient,e.property]
  · intro e
    simp [compactView,ofCompact,rationalLookup_map,CompactRationalSparseData.weightView,e.property]

def step (S : MaterializedRationalSparseData d n) (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n → RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n → ℚ) (alpha lam : ℚ)
    (initial : RationalHistoryData d) (query : RationalGradientQuery d) : MaterializedRationalSparseData d n :=
  let current := (S.compactView live initial).ambient initial
  let output := (countedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam current query).1
  { histories := (next.sort (·≤·)).map (fun e => (e,keyedLookup initial output.histories e))
    weights := output.weights }

theorem step_compactView (hd : 0 < d) {D : ℝ} (W : Domain d D)
    (S : MaterializedRationalSparseData d n) (p roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : Fin n → RationalHistoryParameters) (lo : Fin n → ℝ) (hi : ℝ)
    (hlo : ∀ e, 0 < lo e) (hhi : 0 < hi) (hguard : ∀ e, UniformHistoryGuards d (cfg e) (lo e) hi)
    (live next : Finset (Fin n)) (prior : Fin n → ℚ) (alpha lam : ℚ)
    (initial : RationalHistoryData d) (query : RationalGradientQuery d)
    (hS : RationalSparseInvariant W lo hi live ((S.compactView live initial).ambient initial)) :
    (S.step p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam initial query).compactView next initial=
      (S.compactView live initial).step oracle cfg p lam next prior alpha initial
        (query (S.compactView live initial).prediction) := by
  let C := S.compactView live initial
  let A := C.ambient initial
  have hp : rationalSparsePrediction A=C.prediction := C.ambient_prediction initial
  have hh := countedRationalRound_histories hd W p roundCost projectionCost gradientCost oracle hspec cfg
    lo hi hlo hhi hguard live next prior alpha lam A hS query
  have hw := countedRationalRound_weights p roundCost projectionCost gradientCost oracle cfg live next
    prior alpha lam A query C.weightView_support
  apply CompactRationalSparseData.ext
  · intro e
    change keyedLookup initial ((next.sort (·≤·)).map (fun j =>
      (j,keyedLookup initial (countedRationalRound p roundCost projectionCost gradientCost oracle cfg
        live next prior alpha lam A query).1.histories j))) e.val=_
    rw [keyedLookup_map,if_pos (by simpa using e.property),hh,keyedLookup_map,hp]
    simp only [Finset.mem_sort]
    change (if e.val∈live then _ else initial)=_
    by_cases he : e.val∈live
    · simp [he,C,A,CompactRationalSparseData.ambient,CompactRationalSparseData.step]
    · simp [he,CompactRationalSparseData.step]
  · intro e
    change rationalLookup (countedRationalRound p roundCost projectionCost gradientCost oracle cfg
      live next prior alpha lam A query).1.weights e.val=_
    rw [hw]
    change rationalMasterUpdate p live next C.weightView
      (rationalSparseExponents lam A (query (rationalSparsePrediction A))) prior alpha e.val=_
    rw [hp]
    apply congrFun (rationalMasterUpdate_congr_live p live next C.weightView _ _ prior alpha C.weightView_support ?_) e.val
    intro j hj
    simp only [rationalSparseExponents,CompactRationalSparseData.exponents,dif_pos hj,hp]
    simp only [A,CompactRationalSparseData.ambient,dif_pos hj]
    rfl

theorem step_history_length (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n → RationalHistoryParameters) (live next : Finset (Fin n))
    (prior : Fin n → ℚ) (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (S.step p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam initial query).histories.length=next.card := by
  simp [step]

theorem step_weights_length (S : MaterializedRationalSparseData d n)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n → RationalHistoryParameters) (live next : Finset (Fin n))
    (prior : Fin n → ℚ) (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (S.step p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam initial query).weights.length=next.card := by
  simp only [step,countedRationalRound,countedMasterUpdate_length]

end MaterializedRationalSparseData
end Paper254
#print axioms Paper254.MaterializedRationalSparseData.step_compactView
