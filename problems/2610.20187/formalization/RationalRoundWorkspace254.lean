import HistoryWorkspace254
import RationalMaterializedCost254
import MasterWorkspace254

namespace Paper254

/-- Ownership profile for a sequential map. Input cells belong to the
caller. The returned list is retained while each remaining output is
formed; numerical instruction counters are ghost data. -/
def profiledMap {α β : Type} (outputCells : ℕ) (f : α→(β×ℕ)×ℕ) : List α→(List β×ℕ)×ℕ
  | [] => (([],0),0)
  | x::xs =>
    let tail := profiledMap outputCells f xs
    let item := f x
    ((item.1.1::tail.1.1,item.1.2+tail.1.2),
      max tail.2 (tail.1.1.length*outputCells+item.2+outputCells))

theorem profiledMap_program {α β : Type} (outputCells : ℕ) (f : α→(β×ℕ)×ℕ) (xs : List α) :
    (profiledMap outputCells f xs).1=mapWithCosts (fun x=>(f x).1) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [profiledMap,mapWithCosts,ih]

theorem profiledMap_workspace {α β : Type} (outputCells : ℕ) (f : α→(β×ℕ)×ℕ)
    (xs : List α) (B : ℕ) (hB : ∀ x∈xs,(f x).2≤B) :
    (profiledMap outputCells f xs).2≤xs.length*outputCells+B := by
  induction xs with
  | nil => simp [profiledMap]
  | cons x xs ih =>
    have ht := ih (fun y hy=>hB y (by simp [hy]))
    have hx := hB x (by simp)
    have hlen : (profiledMap outputCells f xs).1.1.length=xs.length := by
      rw [profiledMap_program,mapWithCosts_length]
    simp only [profiledMap,max_le_iff,List.length_cons,hlen]
    constructor <;> nlinarith

def profiledHistoryBatch {d n : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (S : RationalSparseData d n) (lam : ℚ) (g w : Fin d→ℚ) :=
  profiledMap (d*d+d) (fun e=>
    let out := profiledHistoryStep roundCost projectionCost projectionWorkspace oracle (cfg e) (S.histories e) lam g w
    (((e,out.1.1),out.1.2),out.2)) (live.sort (·≤·))

theorem profiledHistoryBatch_program {d n : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (S : RationalSparseData d n) (lam : ℚ) (g w : Fin d→ℚ) :
    (profiledHistoryBatch roundCost projectionCost projectionWorkspace oracle cfg live S lam g w).1=
      countedHistoryBatch roundCost projectionCost oracle cfg live S lam g w := by
  simp only [profiledHistoryBatch,profiledMap_program,profiledHistoryStep_program,countedHistoryBatch]

theorem profiledHistoryBatch_workspace {d n : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live : Finset (Fin n)) (S : RationalSparseData d n) (lam : ℚ) (g w : Fin d→ℚ) :
    (profiledHistoryBatch roundCost projectionCost projectionWorkspace oracle cfg live S lam g w).2≤
      live.card*(d*d+d)+60*(d+1)^2+projectionWorkspace := by
  have hh := profiledMap_workspace (d*d+d) (fun e=>
    let out := profiledHistoryStep roundCost projectionCost projectionWorkspace oracle (cfg e) (S.histories e) lam g w
    (((e,out.1.1),out.1.2),out.2)) (live.sort (·≤·)) (60*(d+1)^2+projectionWorkspace)
    (fun e _=>profiledHistoryStep_workspace roundCost projectionCost projectionWorkspace
      oracle (cfg e) (S.histories e) lam g w)
  simpa only [profiledHistoryBatch,Finset.length_sort,Nat.add_assoc] using hh

/-- Complete-round ownership profile. Old compact state and returned
history/weight lists are counted simultaneously. The master allowance
includes its raw/normalized/upper lists and scalar Taylor/power stacks.
Projection workspace is an explicit external-oracle quantity. -/
def profiledRationalRound {d n : ℕ} (p roundCost projectionCost gradientCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d) :
    (CountedRationalRoundData d n×ℕ)×ℕ :=
  let prediction := countedSparsePrediction live S
  let g := Vector.ofFn (query prediction.1)
  let exponents := countedSparseExponents live lam S (fun j=>g.get j) prediction.1
  let histories := profiledHistoryBatch roundCost projectionCost projectionWorkspace oracle cfg live S lam
    (fun j=>g.get j) prediction.1
  let weights := profiledMasterUpdate p roundCost live next S.weights (rationalLookup exponents.1) prior alpha
  let old := live.card*(d*d+d+1)
  let vectors := 8*d+2*live.card+10
  ((⟨prediction.1,fun j=>g.get j,histories.1.1,weights.1.1⟩,
    prediction.2+gradientCost+exponents.2+histories.1.2+weights.1.2),
    old+max vectors (max (vectors+histories.2)
      (vectors+histories.1.1.length*(d*d+d)+weights.2)))

theorem profiledRationalRound_program {d n : ℕ} (p roundCost projectionCost gradientCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d) :
    (profiledRationalRound p roundCost projectionCost gradientCost projectionWorkspace
      oracle cfg live next prior alpha lam S query).1=
      countedRationalRound p roundCost projectionCost gradientCost oracle cfg live next prior alpha lam S query := by
  simp only [profiledRationalRound,profiledHistoryBatch_program,profiledMasterUpdate_program,countedRationalRound]

def rationalRoundWorkspaceBound (d N M p projectionWorkspace : ℕ) :=
  2*N*(d*d+d+1)+8*d+2*N+10+60*(d+1)^2+24*(N+M+p+1)+projectionWorkspace

theorem profiledRationalRound_workspace {d n : ℕ} (p roundCost projectionCost gradientCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha lam : ℚ)
    (S : RationalSparseData d n) (query : RationalGradientQuery d) :
    (profiledRationalRound p roundCost projectionCost gradientCost projectionWorkspace
      oracle cfg live next prior alpha lam S query).2≤
      rationalRoundWorkspaceBound d live.card next.card p projectionWorkspace := by
  have hh := profiledHistoryBatch_workspace roundCost projectionCost projectionWorkspace oracle cfg live S lam
    (fun j=>(Vector.ofFn (query (countedSparsePrediction live S).1)).get j) (countedSparsePrediction live S).1
  have hm := profiledMasterUpdate_workspace p roundCost live next S.weights
    (rationalLookup (countedSparseExponents live lam S
      (fun j=>(Vector.ofFn (query (countedSparsePrediction live S).1)).get j)
      (countedSparsePrediction live S).1).1) prior alpha
  have hlen : (profiledHistoryBatch roundCost projectionCost projectionWorkspace oracle cfg live S lam
      (fun j=>(Vector.ofFn (query (countedSparsePrediction live S).1)).get j)
      (countedSparsePrediction live S).1).1.1.length=live.card := by
    rw [profiledHistoryBatch_program]
    simp only [countedHistoryBatch,mapWithCosts_length,Finset.length_sort]
  simp only [profiledRationalRound,rationalRoundWorkspaceBound]
  rw [hlen,add_max,add_max]
  apply max_le
  · nlinarith
  · apply max_le <;> nlinarith

theorem rationalRoundWorkspaceBound_mono (d N M N' M' p projectionWorkspace : ℕ)
    (hN : N≤N') (hM : M≤M') :
    rationalRoundWorkspaceBound d N M p projectionWorkspace≤
      rationalRoundWorkspaceBound d N' M' p projectionWorkspace := by
  unfold rationalRoundWorkspaceBound
  gcongr

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

noncomputable def materializedWorkspace (projectionWorkspace t : ℕ) :=
  let initial := rationalHistoryInitial C.initial_mean C.hi
  let S := ((C.materializedRun 1 0 0 t).compactView
    ((standardRationalSchedule T K).live t) initial).ambient initial
  (profiledRationalRound C.master_precision 1 0 0 projectionWorkspace C.oracle C.allCfg
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
    C.lam S (C.query t)).2

theorem materialized_workspace_bound (projectionWorkspace t : ℕ) :
    C.materializedWorkspace projectionWorkspace t≤rationalRoundWorkspaceBound d
      (standardLiveCap T K) (standardLiveCap T K) C.master_precision projectionWorkspace := by
  apply (profiledRationalRound_workspace C.master_precision 1 0 0 projectionWorkspace
    C.oracle C.allCfg _ _ _ _ C.lam _ (C.query t)).trans
  exact rationalRoundWorkspaceBound_mono _ _ _ _ _ _ _
    (standardRationalSchedule_uniform_card T K t) (standardRationalSchedule_uniform_card T K (t+1))

end RationalSparseConstruction

end Paper254
#print axioms Paper254.profiledRationalRound_program
#print axioms Paper254.profiledRationalRound_workspace
#print axioms Paper254.RationalSparseConstruction.materialized_workspace_bound
