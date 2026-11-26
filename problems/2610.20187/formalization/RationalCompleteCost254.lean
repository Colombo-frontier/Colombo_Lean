import RationalPreparedProgram254
import RationalSetupWidths254
import RationalAllPathImplementation254
import RationalAnytimeImplementation254

noncomputable section
open scoped BigOperators
namespace Paper254

namespace RationalRunEncodingSetup
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable {C : RationalSparseConstruction d T K D G eta W} (E : RationalRunEncodingSetup C)

/-- Primitive model: each charged rational arithmetic/rounding instruction
includes its constant local control and indexed operand access. This same
convention applies to the recursive power/Taylor/Newton and matrix kernels;
their numerical/index capacity is the numerical primitive envelope, not
`metadataWordBits`. This is a compositional arithmetic model, not a claim
about Lean's compiler, allocator or individual machine instructions.

The extra rational division constructs the share scalar. The metadata
term includes scheduling, sorting, decoding, configuration access and
key lookups of the same cached transition. -/
def completeRoundCharge (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost t : ℕ) :=
  E.bitRoundCharge rationalModel projectionCost gradientCost t+
    rationalModel.cost (shareMassHeight T+1)+
    (C.cachedStep t).2*integerModel.cost (metadataWordBits T K)

def completePerRound (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost : ℕ) :=
  E.bitPerRound rationalModel projectionCost gradientCost+
    rationalModel.coefficient*(shareMassHeight T+2)^rationalModel.degree+
    cachedMetadataRoundBound T K d*integerModel.coefficient*
      (metadataWordBits T K+1)^integerModel.degree

theorem complete_round_charge_le (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost t : ℕ) :
    E.completeRoundCharge rationalModel integerModel projectionCost gradientCost t≤
      E.completePerRound rationalModel integerModel projectionCost gradientCost := by
  have hh:=E.bit_round_charge_le rationalModel projectionCost gradientCost t
  have hm:=Nat.mul_le_mul (C.cachedStep_metadata t) (integerModel.bound (metadataWordBits T K))
  have hs:=rationalModel.bound (shareMassHeight T+1)
  simpa only [completeRoundCharge,completePerRound,Nat.add_assoc,Nat.mul_assoc] using
    Nat.add_le_add (Nat.add_le_add hh hs) hm

theorem complete_prefix_charge (rationalModel integerModel : PolynomialArithmeticCharge)
    (projectionCost gradientCost R : ℕ) :
    (∑ t : Fin R,E.completeRoundCharge rationalModel integerModel projectionCost gradientCost t)≤
      R*E.completePerRound rationalModel integerModel projectionCost gradientCost := by
  calc _≤∑ _t : Fin R,E.completePerRound rationalModel integerModel projectionCost gradientCost :=
        Finset.sum_le_sum (fun t _=>E.complete_round_charge_le rationalModel integerModel projectionCost gradientCost t)
       _=_ := by simp

/-- A prefix is valid only for responses actually covered by the encoding
interface. The theorem records this condition explicitly alongside the
cost and the actual cached transition refinement. -/
theorem complete_prefix_certificate (R : ℕ) (hRT : R≤T) (hresponse : R≤E.responseHorizon)
    (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    (∀ t<R,(C.cachedStep t).1.1=C.materializedRun 1 0 0 (t+1)) ∧
    (∀ t<R,∀ e,HistoryWorkHeights C.oracle (C.allCfg e) ((C.run t).histories e) C.lam
      (C.gradient t) (C.prediction t) E.uniformHistoryHeight) ∧
    (∀ t<R,MasterWorkHeights C.master_precision ((standardRationalSchedule T K).live t)
      ((standardRationalSchedule T K).live (t+1)) (C.run t).weights
      (rationalSparseExponents C.lam (C.run t) (C.gradient t))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      E.uniformMasterHeight) ∧
    (∀ t<R,RationalHeight (1/(t+2:ℚ)) (shareMassHeight T)) ∧
    (∑ t : Fin R,E.completeRoundCharge rationalModel integerModel projectionCost gradientCost t)≤
      R*E.completePerRound rationalModel integerModel projectionCost gradientCost := by
  refine ⟨fun t _=>C.cachedStep_program t,fun t ht e=>E.uniform_history_work t (lt_of_lt_of_le ht hresponse) e,
    fun t ht=>E.master_work_heights t (lt_of_lt_of_le ht hRT) (lt_of_lt_of_le ht hresponse),?_,
    E.complete_prefix_charge rationalModel integerModel projectionCost gradientCost R⟩
  intro t ht
  exact rational_share_mass_height T t (by omega)

end RationalRunEncodingSetup

namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

/-- This capacity covers the cached parameter constructor, initial scalar
writes, the common rational prior and the initialization's integer indices.
Precision exponents are part of the explicit input to this constructor. -/
def preparationBits (b : ℕ) := parameterSetupWorkHeight d (scaleCount T) I.s I.v b+
  initialMassHeight (scaleCount T)+metadataWordBits T (scaleCount T)+d+I.s+I.v+20

def preparationCharge (b : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) :=
  I.preparation.1.2*rationalModel.cost (I.preparationBits b)+
    I.preparation.2*integerModel.cost (I.preparationBits b)

def preparationBound (b : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) :=
  I.preparationRationalBound*rationalModel.coefficient*(I.preparationBits b+1)^rationalModel.degree+
    I.preparationMetadataBound*integerModel.coefficient*(I.preparationBits b+1)^integerModel.degree

theorem preparation_charge_le (b : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) :
    I.preparationCharge b rationalModel integerModel≤I.preparationBound b rationalModel integerModel := by
  have hr:=Nat.mul_le_mul I.preparation_rational (rationalModel.bound (I.preparationBits b))
  have hi:=Nat.mul_le_mul I.preparation_metadata (integerModel.bound (I.preparationBits b))
  simpa only [preparationCharge,preparationBound,Nat.mul_assoc] using Nat.add_le_add hr hi

/-- The numerical parameter constructor has an operand certificate derived
from the input height; no encoded evolved state is assumed. -/
theorem preparation_work_heights (b : ℕ) (hhi : RationalHeight I.hi b) :
    ParameterSetupWorkHeights d (scaleCount T) I.s I.v I.hi
      (parameterSetupWorkHeight d (scaleCount T) I.s I.v b) ∧
    RationalHeight I.preparation.1.1.priorMass (initialMassHeight (scaleCount T)) :=
  ⟨countedParameterSetup_work_heights d (scaleCount T) I.s I.v b I.hi hhi,
    rational_initial_mass_height (scaleCount T)⟩

end ExplicitRationalSparseInput

/-- Actual cached setup followed by the actual executed prefix. -/
def completeImplementationCharge {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W)
    {oracle : RationalLossGradientOracle d} {hspec : RationalLossGradientOracleSpec W G eta oracle}
    {f : ℕ→Loss d} (E : RationalRunEncodingSetup (I.construction.forLosses oracle hspec f))
    (b R : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :=
  I.preparationCharge b rationalModel integerModel+
    ∑ t : Fin R,E.completeRoundCharge rationalModel integerModel projectionCost gradientCost t

theorem complete_implementation_charge {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W)
    {oracle : RationalLossGradientOracle d} {hspec : RationalLossGradientOracleSpec W G eta oracle}
    {f : ℕ→Loss d} (E : RationalRunEncodingSetup (I.construction.forLosses oracle hspec f))
    (b R : ℕ) (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    completeImplementationCharge I E b R rationalModel integerModel projectionCost gradientCost≤
      I.preparationBound b rationalModel integerModel+
        R*E.completePerRound rationalModel integerModel projectionCost gradientCost :=
  Nat.add_le_add (I.preparation_charge_le b rationalModel integerModel)
    (E.complete_prefix_charge rationalModel integerModel projectionCost gradientCost R)

end Paper254
#print axioms Paper254.RationalRunEncodingSetup.complete_prefix_certificate
#print axioms Paper254.ExplicitRationalSparseInput.preparation_work_heights
#print axioms Paper254.complete_implementation_charge

