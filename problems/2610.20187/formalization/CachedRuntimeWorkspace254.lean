import RationalPreparedProgram254
import RationalRoundWorkspace254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- An owned-cell model: rational payload cells and integer/reference cells
are counted separately. Released intermediates are reusable. The profiles
are mathematical resource annotations, not claims about a native allocator. -/
structure OwnedCellProfile where
  rational : ℕ
  integer : ℕ

/-- The five stored integer fields and the two derived loop/rounding bounds.
This also bounds every recursive counter in the corresponding numerical
history kernel; ghost instruction counters are not retained program data. -/
def cfgIndexAllowance (cfg : RationalHistoryParameters) : ℕ :=
  cfg.dimensionLog+cfg.spectralLog+cfg.accuracy+cfg.storagePrecision+cfg.projectionPrecision+
    matrixSqrtIterations cfg.dimensionLog cfg.spectralLog cfg.accuracy+
    matrixSqrtPrecision cfg.dimensionLog cfg.spectralLog cfg.accuracy+10

def cachedCfgIndexAllowance {K : ℕ} (rows : Vector RationalHistoryParameters (K+1)) : ℕ :=
  ∑ k : Fin (K+1),cfgIndexAllowance (rows.get k)

theorem cfgIndexAllowance_le {K : ℕ} (rows : Vector RationalHistoryParameters (K+1))
    (k : Fin (K+1)) : cfgIndexAllowance (rows.get k)≤cachedCfgIndexAllowance rows := by
  unfold cachedCfgIndexAllowance
  exact Finset.single_le_sum (fun j _=>Nat.zero_le (cfgIndexAllowance (rows.get j))) (Finset.mem_univ k)

/-- Candidate/filter/dedup/sort lists, their recursion frames, the expanded
key list and its sorting frames are simultaneously over-allocated here.
Each list cell reserves a value and links; scalar log/power frames are
included. Integer payload bounds are supplied separately. -/
def scheduleIntegerCells (T K t : ℕ) : ℕ :=
  let clock := min t T+1
  let candidates := (countedCandidateList clock).1
  let expanded := (countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList clock).1).1
  32*candidates.length+24*expanded.length+16*(Nat.log 2 clock+1)+32

def scheduleIntegerCellBound (T K : ℕ) : ℕ :=
  176*(Nat.log 2 (T+1)+1)+24*standardLiveCap T K+32

theorem schedule_integer_cells_bound (T K t : ℕ) :
    scheduleIntegerCells T K t≤scheduleIntegerCellBound T K := by
  have hd : Nat.log 2 (min t T+1)+1≤Nat.log 2 (T+1)+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have he : (countedFlatMap (countedHistoryKeys T K)
      (countedShortHistoryList (min t T+1)).1).1.length≤standardLiveCap T K := by
    rw [countedExpandedLive_value,List.length_map]
    apply (shortLiveList_length T K _).trans
    unfold standardLiveCap
    gcongr
  simp only [scheduleIntegerCells,countedCandidateList_length,scheduleIntegerCellBound]
  omega

namespace PreparedRationalData
variable {d T K : ℕ} (P : PreparedRationalData d T K)

/-- The prepared initial state is retained conservatively even if an
implementation releases it after the first transition. Shared Gaussians
may therefore be counted more than once, which is safe for an upper bound. -/
def retainedRationalCells := d*d+d+3*(K+1)+
  P.state.histories.length*(d*d+d)+P.state.weights.length+3

def retainedIntegerCells := 5*(K+1)+3*(P.state.histories.length+P.state.weights.length)+10

end PreparedRationalData

def preparedRationalCellBound (d T K : ℕ) :=
  d*d+d+3*(K+1)+standardLiveCap T K*(d*d+d+1)+3

def preparedIntegerCellBound (T K : ℕ) := 5*(K+1)+6*standardLiveCap T K+10

theorem prepared_retained_cells_bound {d T K : ℕ} (P : PreparedRationalData d T K)
    (hH : P.state.histories.length≤standardLiveCap T K)
    (hW : P.state.weights.length≤standardLiveCap T K) :
    P.retainedRationalCells≤preparedRationalCellBound d T K ∧
      P.retainedIntegerCells≤preparedIntegerCellBound T K := by
  have hm := Nat.mul_le_mul_right (d*d+d) hH
  simp only [PreparedRationalData.retainedRationalCells,preparedRationalCellBound,
    PreparedRationalData.retainedIntegerCells,preparedIntegerCellBound]
  constructor <;> nlinarith

/-- Complete cached-transition annotation. It retains prepared inputs,
the old list state, both actual schedule lists, numerical-round workspace,
and the pruning output simultaneously. The integer reserve includes list
links, lookup/sort frames, configuration rows, matrix coordinates and
precision/iteration stacks. The two oracle workspaces are explicit. -/
def profiledPreparedStep {d T K : ℕ} (P : PreparedRationalData d T K)
    (t p projectionWorkspace gradientWorkspace : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (oracle : RationalProjectionProcedure d) (lam : ℚ) (query : RationalGradientQuery d) :
    ((MaterializedRationalSparseData d ((T+1)*(K+1))×ℕ)×ℕ)×OwnedCellProfile :=
  let live := (fullyCountedStandardLive T K t).1
  let next := (fullyCountedStandardLive T K (t+1)).1
  let prior := cachedPriorWithCost T K ⟨min (t+1) T,by omega⟩ P.priorMass
  let numerical := profiledRationalRound p 1 0 0 projectionWorkspace oracle
    (fun e=>(countedCfgLookup T K P.rows e).1)
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    (fun e=>(prior e).1) (1/(t+2:ℚ)) lam
    ((S.compactView ((standardRationalSchedule T K).live t) P.initial).ambient P.initial) query
  let out := cachedScheduledStep T K t S p 1 0 0 oracle P.rows P.priorMass lam P.initial query
  (out,⟨P.retainedRationalCells+S.histories.length*(d*d+d)+S.weights.length+
      numerical.2+next.length*(d*d+d)+gradientWorkspace+8,
    P.retainedIntegerCells+scheduleIntegerCells T K t+scheduleIntegerCells T K (t+1)+
      20*(live.length+next.length+S.histories.length+S.weights.length)+
      16*(d*d+d+p+cachedCfgIndexAllowance P.rows+10)⟩)

theorem profiledPreparedStep_program {d T K : ℕ} (P : PreparedRationalData d T K)
    (t p projectionWorkspace gradientWorkspace : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (oracle : RationalProjectionProcedure d) (lam : ℚ) (query : RationalGradientQuery d) :
    (profiledPreparedStep P t p projectionWorkspace gradientWorkspace S oracle lam query).1=
      cachedScheduledStep T K t S p 1 0 0 oracle P.rows P.priorMass lam P.initial query := rfl

def cachedRationalCellBound (d T K p projectionWorkspace gradientWorkspace : ℕ) :=
  preparedRationalCellBound d T K+standardLiveCap T K*(d*d+d+1)+
    rationalRoundWorkspaceBound d (standardLiveCap T K) (standardLiveCap T K) p projectionWorkspace+
    standardLiveCap T K*(d*d+d)+gradientWorkspace+8

def cachedIntegerCellBound {K : ℕ} (d T p : ℕ)
    (rows : Vector RationalHistoryParameters (K+1)) :=
  preparedIntegerCellBound T K+2*scheduleIntegerCellBound T K+80*standardLiveCap T K+
    16*(d*d+d+p+cachedCfgIndexAllowance rows+10)

theorem profiledPreparedStep_workspace {d T K : ℕ} (P : PreparedRationalData d T K)
    (t p projectionWorkspace gradientWorkspace : ℕ)
    (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (oracle : RationalProjectionProcedure d) (lam : ℚ) (query : RationalGradientQuery d)
    (hPH : P.state.histories.length≤standardLiveCap T K)
    (hPW : P.state.weights.length≤standardLiveCap T K)
    (hH : S.histories.length≤standardLiveCap T K)
    (hW : S.weights.length≤standardLiveCap T K) :
    (profiledPreparedStep P t p projectionWorkspace gradientWorkspace S oracle lam query).2.rational≤
      cachedRationalCellBound d T K p projectionWorkspace gradientWorkspace ∧
    (profiledPreparedStep P t p projectionWorkspace gradientWorkspace S oracle lam query).2.integer≤
      cachedIntegerCellBound d T p P.rows := by
  have hP := prepared_retained_cells_bound P hPH hPW
  have hl (j : ℕ) : (fullyCountedStandardLive T K j).1.length≤standardLiveCap T K := by
    rw [fullyCountedStandardLive_program,Finset.length_sort]
    exact standardRationalSchedule_uniform_card T K j
  have hn := profiledRationalRound_workspace p 1 0 0 projectionWorkspace oracle
    (fun e=>(countedCfgLookup T K P.rows e).1)
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    (fun e=>(cachedPriorWithCost T K ⟨min (t+1) T,by omega⟩ P.priorMass e).1)
    (1/(t+2:ℚ)) lam
    ((S.compactView ((standardRationalSchedule T K).live t) P.initial).ambient P.initial) query
  have hnum := hn.trans (rationalRoundWorkspaceBound_mono d _ _ _ _ p projectionWorkspace
    (standardRationalSchedule_uniform_card T K t) (standardRationalSchedule_uniform_card T K (t+1)))
  have hs := schedule_integer_cells_bound T K t
  have hs' := schedule_integer_cells_bound T K (t+1)
  have hl0 := hl t
  have hl1 := hl (t+1)
  have hmH := Nat.mul_le_mul_right (d*d+d) hH
  have hmN := Nat.mul_le_mul_right (d*d+d) hl1
  simp only [profiledPreparedStep,cachedRationalCellBound,cachedIntegerCellBound]
  constructor <;> nlinarith

/-- A universal storage word also accommodates dimension/precision
indices and references into the owned-cell arena. Schedule-only keys retain
the sharper metadataWordBits certificate proved separately. -/
def cachedIntegerCapacity {K : ℕ} (d T p totalCells : ℕ)
    (rows : Vector RationalHistoryParameters (K+1)) :=
  metadataWordBound T K+d*d+d+p+cachedCfgIndexAllowance rows+totalCells+16

def cachedIntegerBits {K : ℕ} (d T p totalCells : ℕ)
    (rows : Vector RationalHistoryParameters (K+1)) :=
  Nat.log 2 (cachedIntegerCapacity d T p totalCells rows+1)+1

theorem cached_integer_size {K : ℕ} (d T p totalCells x : ℕ)
    (rows : Vector RationalHistoryParameters (K+1))
    (hx : x≤cachedIntegerCapacity d T p totalCells rows) :
    x.size≤cachedIntegerBits d T p totalCells rows := by
  apply Nat.size_le.mpr
  exact (by omega : x≤cachedIntegerCapacity d T p totalCells rows+1).trans_lt
    (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) _)

theorem cached_integer_component_bits {K : ℕ} (d T p totalCells : ℕ)
    (rows : Vector RationalHistoryParameters (K+1)) :
    (∀ x≤metadataWordBound T K,x.size≤cachedIntegerBits d T p totalCells rows) ∧
    (∀ x≤d*d+d+p,x.size≤cachedIntegerBits d T p totalCells rows) ∧
    (∀ k : Fin (K+1),∀ x≤cfgIndexAllowance (rows.get k),
      x.size≤cachedIntegerBits d T p totalCells rows) ∧
    (∀ x≤totalCells,x.size≤cachedIntegerBits d T p totalCells rows) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx; apply cached_integer_size; unfold cachedIntegerCapacity; omega
  · intro x hx; apply cached_integer_size; unfold cachedIntegerCapacity; omega
  · intro k x hx
    have hk := cfgIndexAllowance_le rows k
    apply cached_integer_size
    unfold cachedIntegerCapacity
    omega
  · intro x hx; apply cached_integer_size; unfold cachedIntegerCapacity; omega

/-- One sign bit and two bounded integer payloads encode a rational cell;
integer/reference cells use the separately certified capacity. -/
def OwnedCellProfile.bitBudget (P : OwnedCellProfile) (rationalBits integerBits : ℕ) :=
  P.rational*(2*rationalBits+1)+P.integer*integerBits

theorem owned_bit_budget_mono (P : OwnedCellProfile) (R I rbits ibits : ℕ)
    (hR : P.rational≤R) (hI : P.integer≤I) :
    P.bitBudget rbits ibits≤R*(2*rbits+1)+I*ibits := by
  unfold OwnedCellProfile.bitBudget
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hR) (Nat.mul_le_mul_right _ hI)

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem prepared_run_owned_cells (P : PreparedRationalData d T K)
    (hrows : P.rows=C.cachedRows) (hinit : P.initial=rationalHistoryInitial C.initial_mean C.hi)
    (hstate : P.state=C.materializedRun 1 0 0 0) (hmass : P.priorMass=1/(K+1:ℚ))
    (t projectionWorkspace gradientWorkspace : ℕ) :
    let S := preparedRun P C.master_precision C.oracle C.lam C.query t
    let out := profiledPreparedStep P t C.master_precision projectionWorkspace gradientWorkspace S
      C.oracle C.lam (C.query t)
    out.1.1.1=preparedRun P C.master_precision C.oracle C.lam C.query (t+1) ∧
      out.2.rational≤cachedRationalCellBound d T K C.master_precision projectionWorkspace gradientWorkspace ∧
      out.2.integer≤cachedIntegerCellBound d T C.master_precision P.rows := by
  dsimp only
  constructor
  · rfl
  · apply profiledPreparedStep_workspace
    · rw [hstate,C.materializedRun_history_length]
      exact standardRationalSchedule_uniform_card T K 0
    · rw [hstate,C.materializedRun_weights_length]
      exact standardRationalSchedule_uniform_card T K 0
    · rw [C.preparedRun_refines P hrows hinit hstate hmass,C.materializedRun_history_length]
      exact standardRationalSchedule_uniform_card T K t
    · rw [C.preparedRun_refines P hrows hinit hstate hmass,C.materializedRun_weights_length]
      exact standardRationalSchedule_uniform_card T K t

/-- Combining the actual owned-cell profile with a supplied rational
payload capacity. The capacity can be instantiated by the numerical-work
certificates, enlarged for retained inputs and external oracle workspaces.
Reference and integer payload widths are computed from the arena bound. -/
theorem prepared_run_owned_bit_budget (P : PreparedRationalData d T K)
    (hrows : P.rows=C.cachedRows) (hinit : P.initial=rationalHistoryInitial C.initial_mean C.hi)
    (hstate : P.state=C.materializedRun 1 0 0 0) (hmass : P.priorMass=1/(K+1:ℚ))
    (t projectionWorkspace gradientWorkspace rationalBits : ℕ) :
    let R := cachedRationalCellBound d T K C.master_precision projectionWorkspace gradientWorkspace
    let I := cachedIntegerCellBound d T C.master_precision P.rows
    let B := cachedIntegerBits d T C.master_precision (R+I) P.rows
    let S := preparedRun P C.master_precision C.oracle C.lam C.query t
    let out := profiledPreparedStep P t C.master_precision projectionWorkspace gradientWorkspace S
      C.oracle C.lam (C.query t)
    out.2.bitBudget rationalBits B≤R*(2*rationalBits+1)+I*B := by
  dsimp only
  have hh := C.prepared_run_owned_cells P hrows hinit hstate hmass t projectionWorkspace gradientWorkspace
  exact owned_bit_budget_mono _ _ _ _ _ hh.2.1 hh.2.2

end RationalSparseConstruction
end Paper254
#print axioms Paper254.profiledPreparedStep_program
#print axioms Paper254.profiledPreparedStep_workspace
#print axioms Paper254.cached_integer_component_bits
#print axioms Paper254.RationalSparseConstruction.prepared_run_owned_cells
#print axioms Paper254.RationalSparseConstruction.prepared_run_owned_bit_budget
