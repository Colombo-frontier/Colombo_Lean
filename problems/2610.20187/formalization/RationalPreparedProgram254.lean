import RationalCachedRuntime254
import RationalRunBitCost254
import MetadataWidth254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- These are the values retained between initialization and the run.
All scale configurations, the initial Gaussian, and the common birth mass
are built once and shared by subsequent transitions. -/
structure PreparedRationalData (d T K : ℕ) where
  rows : Vector RationalHistoryParameters (K+1)
  initial : RationalHistoryData d
  state : MaterializedRationalSparseData d ((T+1)*(K+1))
  priorMass : ℚ

def countedSparsePreparation {d : ℕ} (T K : ℕ) (w0 : Fin d→ℚ) (hi : ℚ)
    (parameters : (Vector RationalHistoryParameters (K+1)×ℕ)×ℕ) :
    (PreparedRationalData d T K×ℕ)×ℕ :=
  let live := fullyCountedStandardLive T K 0
  let gaussian := countedInitialGaussian w0 hi
  let mass : ℚ := 1/(K+1:ℚ)
  let histories := mapWithCosts (fun e=>((e,gaussian.1.1),1)) live.1
  let weights := mapWithCosts (fun e=>((e,mass),1)) live.1
  ((⟨parameters.1.1,gaussian.1.1,⟨histories.1,weights.1⟩,mass⟩,
    gaussian.1.2+1+parameters.1.2),
    live.2+gaussian.2+histories.2+weights.2+2+parameters.2)

theorem countedSparsePreparation_state {d : ℕ} (T K : ℕ) (w0 : Fin d→ℚ) (hi : ℚ)
    (parameters : (Vector RationalHistoryParameters (K+1)×ℕ)×ℕ) :
    (countedSparsePreparation T K w0 hi parameters).1.1.state=
      (countedRationalInitialization T K w0 hi).1.1 := rfl

def preparedRun {d T K : ℕ} (P : PreparedRationalData d T K)
    (p : ℕ) (oracle : RationalProjectionProcedure d) (lam : ℚ)
    (query : ℕ→RationalGradientQuery d) : ℕ→MaterializedRationalSparseData d ((T+1)*(K+1))
  | 0 => P.state
  | t+1 => (cachedScheduledStep T K t (preparedRun P p oracle lam query t)
      p 1 0 0 oracle P.rows P.priorMass lam P.initial (query t)).1.1

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def cachedRows : Vector RationalHistoryParameters (K+1) := Vector.ofFn C.cfg

theorem cachedRows_lookup (e : Fin ((T+1)*(K+1))) :
    (countedCfgLookup T K C.cachedRows e).1=C.allCfg e := by
  simp [countedCfgLookup,cachedRows,Vector.get,allCfg,numberedExpertEquiv,finProdFinEquiv,Fin.modNat]

theorem preparedRun_refines (P : PreparedRationalData d T K)
    (hrows : P.rows=C.cachedRows) (hinit : P.initial=rationalHistoryInitial C.initial_mean C.hi)
    (hstate : P.state=C.materializedRun 1 0 0 0) (hmass : P.priorMass=1/(K+1:ℚ)) (t : ℕ) :
    preparedRun P C.master_precision C.oracle C.lam C.query t=C.materializedRun 1 0 0 t := by
  induction t with
  | zero => exact hstate
  | succ t ih =>
    simp only [preparedRun,ih,hrows,hinit,hmass,cachedScheduledStep_program]
    simp only [cachedRows_lookup]
    rfl

def cachedStep (t : ℕ) := cachedScheduledStep T K t (C.materializedRun 1 0 0 t)
  C.master_precision 1 0 0 C.oracle C.cachedRows (1/(K+1:ℚ)) C.lam
  (rationalHistoryInitial C.initial_mean C.hi) (C.query t)

theorem cachedStep_program (t : ℕ) :
    (C.cachedStep t).1.1=C.materializedRun 1 0 0 (t+1) := by
  simp only [cachedStep,cachedScheduledStep_program,cachedRows_lookup]
  rfl

theorem cachedStep_rational (t : ℕ) :
    (C.cachedStep t).1.2=
      (countedRationalRound C.master_precision 1 0 0 C.oracle C.allCfg
        ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
        ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) C.lam
        (((C.materializedRun 1 0 0 t).compactView ((standardRationalSchedule T K).live t)
          (rationalHistoryInitial C.initial_mean C.hi)).ambient (rationalHistoryInitial C.initial_mean C.hi))
        (C.query t)).2+1 := by
  simp only [cachedStep,cachedScheduledStep_rational,cachedRows_lookup]

theorem cachedStep_metadata (t : ℕ) : (C.cachedStep t).2≤cachedMetadataRoundBound T K d := by
  apply cachedScheduledStep_metadata
  · rw [C.materializedRun_history_length]
    exact standardRationalSchedule_uniform_card T K t
  · rw [C.materializedRun_weights_length]
    exact standardRationalSchedule_uniform_card T K t

end RationalSparseConstruction

namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

def preparation := countedSparsePreparation T (scaleCount T) I.initial_mean I.hi
  (countedParameterSetup d (scaleCount T) I.s I.v I.hi)

def preparationRationalBound := d*d+d+1+parameterSetupRationalBound d (scaleCount T) I.s I.v

def preparationMetadataBound (_I : ExplicitRationalSparseInput d T D G eta W) := initializationMetadataBound T (scaleCount T) d+20+4*(scaleCount T+1)

theorem preparation_rational : I.preparation.1.2≤I.preparationRationalBound := by
  have hh:=countedParameterSetup_rational d (scaleCount T) I.s I.v I.hi
  simp only [preparation,countedSparsePreparation,countedInitialGaussian,preparationRationalBound]
  omega

theorem preparation_metadata : I.preparation.2≤I.preparationMetadataBound := by
  have hh:=initialization_metadata_charge T (scaleCount T) I.initial_mean I.hi
  simp only [preparation,countedSparsePreparation,countedParameterSetup,preparationMetadataBound]
  simp only [countedRationalInitialization] at hh
  omega

theorem preparation_rows : I.preparation.1.1.rows=I.construction.cachedRows := by
  apply Vector.ext
  intro k hk
  simpa [preparation,countedSparsePreparation,RationalSparseConstruction.cachedRows,Vector.get] using I.parameterSetup_program ⟨k,hk⟩

theorem preparation_initial : I.preparation.1.1.initial=
    rationalHistoryInitial I.initial_mean I.hi := countedInitialGaussian_value _ _

theorem preparation_state : I.preparation.1.1.state=I.construction.materializedRun 1 0 0 0 :=
  I.construction.initialization_program

theorem preparation_mass : I.preparation.1.1.priorMass=1/(scaleCount T+1:ℚ) := rfl

theorem preparation_run (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (f : ℕ→Loss d) (t : ℕ) :
    let C:=I.construction.forLosses oracle hspec f
    preparedRun I.preparation.1.1 C.master_precision C.oracle C.lam C.query t=C.materializedRun 1 0 0 t := by
  intro C
  exact C.preparedRun_refines I.preparation.1.1 I.preparation_rows I.preparation_initial
    I.preparation_state I.preparation_mass t

end ExplicitRationalSparseInput
end Paper254
#print axioms Paper254.RationalSparseConstruction.preparedRun_refines
#print axioms Paper254.RationalSparseConstruction.cachedStep_rational
#print axioms Paper254.ExplicitRationalSparseInput.preparation_run


