import RationalCompleteAnytimeCost254
import RationalPrecisionSetup254

noncomputable section
open scoped BigOperators
namespace Paper254

def precisionCharge (d T b z : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  (countedPrecisionSetup d T b z).2*integerModel.cost (precisionSetupWordBits d T b z)

def precisionChargeBound (d T b z : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  (6*Nat.log 2 (T+1)+27)*integerModel.coefficient*(precisionSetupWordBits d T b z+1)^integerModel.degree

theorem precision_charge_le (d T b z : ℕ) (integerModel : PolynomialArithmeticCharge) :
    precisionCharge d T b z integerModel≤precisionChargeBound d T b z integerModel := by
  simpa only [precisionCharge,precisionChargeBound,Nat.mul_assoc] using
    Nat.mul_le_mul (countedPrecisionSetup_cost_bound d T b z)
      (integerModel.bound (precisionSetupWordBits d T b z))

/-- A joint certificate for the same initialized and cached trajectory.
All operand certificates are restricted to the actually executed prefix;
no height hypothesis is placed on its evolved states. -/
structure CompleteImplementationCertificate {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ→Loss d) (E : RationalRunEncodingSetup (I.construction.forLosses oracle hspec f))
    (b R : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) : Prop where
  horizon : R≤T
  responses : R≤E.responseHorizon
  initial_mean : RationalVectorBits I.initial_mean b
  initial_covariance : RationalHeight I.hi b
  rate_height : RationalHeight I.lam b
  preparation_work : ParameterSetupWorkHeights d (scaleCount T) I.s I.v I.hi
    (parameterSetupWorkHeight d (scaleCount T) I.s I.v b)
  birth_mass : RationalHeight I.preparation.1.1.priorMass (initialMassHeight (scaleCount T))
  actual_run : ∀ t,preparedRun I.preparation.1.1 (I.construction.forLosses oracle hspec f).master_precision
    (I.construction.forLosses oracle hspec f).oracle (I.construction.forLosses oracle hspec f).lam
    (I.construction.forLosses oracle hspec f).query t=(I.construction.forLosses oracle hspec f).materializedRun 1 0 0 t
  history_work : ∀ t<R,∀ e,HistoryWorkHeights (I.construction.forLosses oracle hspec f).oracle
    ((I.construction.forLosses oracle hspec f).allCfg e)
    (((I.construction.forLosses oracle hspec f).run t).histories e)
    (I.construction.forLosses oracle hspec f).lam ((I.construction.forLosses oracle hspec f).gradient t)
    ((I.construction.forLosses oracle hspec f).prediction t) E.uniformHistoryHeight
  master_work : ∀ t<R,MasterWorkHeights (I.construction.forLosses oracle hspec f).master_precision
    ((standardRationalSchedule T (scaleCount T)).live t) ((standardRationalSchedule T (scaleCount T)).live (t+1))
    ((I.construction.forLosses oracle hspec f).run t).weights
    (rationalSparseExponents (I.construction.forLosses oracle hspec f).lam
      ((I.construction.forLosses oracle hspec f).run t) ((I.construction.forLosses oracle hspec f).gradient t))
    ((standardRationalSchedule T (scaleCount T)).prior t) ((standardRationalSchedule T (scaleCount T)).share t)
    E.uniformMasterHeight
  share_work : ∀ t<R,RationalHeight (1/(t+2:ℚ)) (shareMassHeight T)
  total_charge : completeImplementationCharge I E b R rationalModel integerModel projectionCost gradientCost≤
    I.preparationBound b rationalModel integerModel+R*E.completePerRound rationalModel integerModel projectionCost gradientCost

theorem complete_implementation_certificate {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ→Loss d) (E : RationalRunEncodingSetup (I.construction.forLosses oracle hspec f))
    (b R : ℕ) (hRT : R≤T) (hresponse : R≤E.responseHorizon)
    (hmean : RationalVectorBits I.initial_mean b) (hhi : RationalHeight I.hi b) (hlam : RationalHeight I.lam b)
    (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    CompleteImplementationCertificate I oracle hspec f E b R rationalModel integerModel projectionCost gradientCost := by
  have hc:=E.complete_prefix_certificate R hRT hresponse rationalModel integerModel projectionCost gradientCost
  exact ⟨hRT,hresponse,hmean,hhi,hlam,(I.preparation_work_heights b hhi).1,
    (I.preparation_work_heights b hhi).2,I.preparation_run oracle hspec f,hc.2.1,hc.2.2.1,hc.2.2.2.1,
    complete_implementation_charge I E b R rationalModel integerModel projectionCost gradientCost⟩

/-- Epoch precision uses z+j+1. The extra two integer operations form this
exponent; z itself is a supplied input and no real-number search is hidden. -/
def epochPrecisionCharge (d b z j : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  precisionCharge d (2^j) b (z+j+1) integerModel+
    2*integerModel.cost (precisionSetupWordBits d (2^j) b (z+j+1))

def epochPrecisionBound (d b z j : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  precisionChargeBound d (2^j) b (z+j+1) integerModel+
    2*integerModel.coefficient*(precisionSetupWordBits d (2^j) b (z+j+1)+1)^integerModel.degree

theorem epoch_precision_charge_le (d b z j : ℕ) (integerModel : PolynomialArithmeticCharge) :
    epochPrecisionCharge d b z j integerModel≤epochPrecisionBound d b z j integerModel := by
  have hh:=Nat.mul_le_mul_left 2 (integerModel.bound (precisionSetupWordBits d (2^j) b (z+j+1)))
  simpa only [epochPrecisionCharge,epochPrecisionBound,Nat.mul_assoc] using
    Nat.add_le_add (precision_charge_le d (2^j) b (z+j+1) integerModel) hh

def anytimePrecisionCharge (d T b z : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  ∑ j : Fin (epochCount T),epochPrecisionCharge d b z j.val integerModel

def anytimePrecisionBound (d T b z : ℕ) (integerModel : PolynomialArithmeticCharge) :=
  epochCount T*Finset.univ.sup (fun j : Fin (epochCount T)=>epochPrecisionBound d b z j.val integerModel)

theorem anytime_precision_charge_le (d T b z : ℕ) (integerModel : PolynomialArithmeticCharge) :
    anytimePrecisionCharge d T b z integerModel≤anytimePrecisionBound d T b z integerModel := by
  unfold anytimePrecisionCharge anytimePrecisionBound
  calc
    _≤∑ _j : Fin (epochCount T),Finset.univ.sup (fun j : Fin (epochCount T)=>epochPrecisionBound d b z j.val integerModel) := by
      apply Finset.sum_le_sum
      intro j _
      exact (epoch_precision_charge_le d b z j.val integerModel).trans
        (Finset.le_sup (f:=fun j : Fin (epochCount T)=>epochPrecisionBound d b z j.val integerModel) (Finset.mem_univ j))
    _=_ := by simp

end Paper254
#print axioms Paper254.complete_implementation_certificate
#print axioms Paper254.anytime_precision_charge_le
