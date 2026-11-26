import RationalPreparedProgram254

open Paper254

namespace PreparedExecution254

-- These declarations deliberately have no `noncomputable` modifier.
-- This gate executes the actual preparation and cached recursive program;
-- it does not replace them by their mathematical value specifications.
def cfg : RationalHistoryParameters where
  dimensionLog := 0
  spectralLog := 2
  accuracy := 1
  storagePrecision := 8
  projectionPrecision := 8
  smoothing := 1/4
  lowerThreshold := 1/4
  upperThreshold := 1

def prepared : PreparedRationalData 1 2 1 :=
  (countedSparsePreparation 2 1 (fun _ : Fin 1=>(0:ℚ)) 1
    ((Vector.replicate 2 cfg,0),0)).1.1

def projection : RationalProjectionProcedure 1 := fun _ _ _ _=>0
def gradients : ℕ→RationalGradientQuery 1 := fun _ _ _=>0

def state (t : ℕ) := preparedRun prepared 2 projection (1/4) gradients t

def prediction (t : ℕ) : ℚ :=
  let S := state t
  let live := (fullyCountedStandardLive 2 1 t).1
  (list_keyedSparsePrediction live (countedKeyedLookup prepared.initial S.histories)
    (countedKeyedLookup 0 S.weights)).1.1 0

def checks (t : ℕ) : Bool :=
  let S := state t
  let live := (fullyCountedStandardLive 2 1 t).1
  decide (prediction t=0) &&
    S.histories.all (fun e=>decide (e.2.mean 0=0)) &&
    decide ((S.weights.map Prod.snd).sum=1) &&
    decide (S.histories.map Prod.fst=live) &&
    decide (S.weights.map Prod.fst=live)

-- Expected active history/scale counts: 2 initially, then 4, then 6.
-- Failure of either execution or any check makes this gate fail to compile.
#eval show IO Unit from do
  let rounds := [0,1,2]
  let snapshots := rounds.map (fun t=>
    (t,(state t).histories.length,(state t).weights.length,
      prediction t,((state t).weights.map Prod.snd).sum,checks t))
  IO.println s!"prepared execution snapshots: {snapshots}"
  if !(rounds.all checks && decide ((rounds.map (fun t=>(state t).histories.length))=[2,4,6])) then
    throw (IO.userError "prepared execution invariant check failed")
  IO.println "prepared execution: PASS"

end PreparedExecution254
