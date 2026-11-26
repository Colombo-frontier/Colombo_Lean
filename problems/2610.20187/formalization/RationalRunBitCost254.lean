import RationalRunMasterWork254
import RationalMaterializedCost254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem HistoryWorkHeights.mono {d b c : ℕ} {oracle : RationalProjectionProcedure d}
    {cfg : RationalHistoryParameters} {S : RationalHistoryData d} {lam : ℚ} {g w : Fin d→ℚ}
    (h : HistoryWorkHeights oracle cfg S lam g w b) (hbc : b≤c) :
    HistoryWorkHeights oracle cfg S lam g w c := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨h1.mono hbc,h2.mono hbc,h3.mono hbc,h4.mono hbc,h5.mono hbc,
    h6.mono hbc,h7.mono hbc,h8.mono hbc,h9.mono hbc,h10.mono hbc⟩

namespace RationalRunEncodingSetup
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable {C : RationalSparseConstruction d T K D G eta W} (E : RationalRunEncodingSetup C)

/-- Only scales, rather than birth times or rounds, occur in this sum. -/
def uniformHistoryHeight := ∑ j : Fin (K+1),
  historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.cfg j)

def uniformHistoryArithmetic (_E : RationalRunEncodingSetup C) :=
  ∑ j : Fin (K+1),historyStepCostBound d 1 0 (C.cfg j)

def primitiveBits := historyPrimitiveBits d E.uniformHistoryHeight+E.uniformMasterBits+
  4*E.inputHeight+4*E.exponentHeight+4*E.predictionBits+d+20

theorem history_height_le (e : Fin ((T+1)*(K+1))) :
    historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.allCfg e)≤E.uniformHistoryHeight := by
  change _ ≤ ∑ j : Fin (K+1),historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.cfg j)
  exact Finset.single_le_sum (f:=fun j : Fin (K+1)=>
    historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.cfg j)) (fun j _=>Nat.zero_le _)
    (Finset.mem_univ (((numberedExpertEquiv T K).symm e).2))

theorem history_arithmetic_le (e : Fin ((T+1)*(K+1))) :
    historyStepCostBound d 1 0 (C.allCfg e)≤E.uniformHistoryArithmetic := by
  change _ ≤ ∑ j : Fin (K+1),historyStepCostBound d 1 0 (C.cfg j)
  exact Finset.single_le_sum (f:=fun j : Fin (K+1)=>historyStepCostBound d 1 0 (C.cfg j))
    (fun j _=>Nat.zero_le _)
    (Finset.mem_univ (((numberedExpertEquiv T K).symm e).2))

theorem uniform_history_work (t : ℕ) (hresponse : t<E.responseHorizon) (e : Fin ((T+1)*(K+1))) :
    HistoryWorkHeights C.oracle (C.allCfg e) ((C.run t).histories e) C.lam
      (C.gradient t) (C.prediction t) E.uniformHistoryHeight :=
  (E.history_work_heights t hresponse e).mono (E.history_height_le e)

def arithmeticPerRound := standardLiveCap T K*
  (E.uniformHistoryArithmetic+5*d+6*C.master_precision+67)+2*C.master_precision+4

/-- Polynomial primitive charging of the same complete cached round,
with each projection and the single gradient query charged separately. -/
def bitRoundCharge (model : PolynomialArithmeticCharge) (projectionCost gradientCost t : ℕ) : ℕ :=
  let initial := rationalHistoryInitial C.initial_mean C.hi
  let S := ((C.materializedRun 1 0 0 t).compactView
    ((standardRationalSchedule T K).live t) initial).ambient initial
  let arithmetic := (countedRationalRound C.master_precision 1 0 0 C.oracle C.allCfg
    ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
    ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
    C.lam S (C.query t)).2
  arithmetic*model.cost E.primitiveBits+
    ((standardRationalSchedule T K).live t).card*projectionCost+gradientCost

def bitPerRound (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :=
  E.arithmeticPerRound*model.coefficient*(E.primitiveBits+1)^model.degree+
    standardLiveCap T K*projectionCost+gradientCost

theorem bit_round_charge_le (model : PolynomialArithmeticCharge)
    (projectionCost gradientCost t : ℕ) :
    E.bitRoundCharge model projectionCost gradientCost t≤E.bitPerRound model projectionCost gradientCost := by
  let initial := rationalHistoryInitial C.initial_mean C.hi
  let S := ((C.materializedRun 1 0 0 t).compactView
    ((standardRationalSchedule T K).live t) initial).ambient initial
  have hc := countedStandardRound_cost C.dimension_pos C.master_precision 1 0 0 C.oracle
    C.allCfg C.lam S (C.query t) t E.uniformHistoryArithmetic E.history_arithmetic_le
  have hc' : (countedRationalRound C.master_precision 1 0 0 C.oracle C.allCfg
      ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      C.lam S (C.query t)).2≤E.arithmeticPerRound := by
    simpa only [arithmeticPerRound,Nat.mul_one,Nat.reduceAdd,Nat.add_zero,Nat.add_assoc] using hc
  have hm := Nat.mul_le_mul hc' (model.bound E.primitiveBits)
  have hp := Nat.mul_le_mul_right projectionCost (standardRationalSchedule_uniform_card T K t)
  simpa only [bitRoundCharge,bitPerRound,Nat.mul_assoc] using
    Nat.add_le_add_right (Nat.add_le_add hm hp) gradientCost

theorem total_bit_charge (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    (∑ t : Fin T,E.bitRoundCharge model projectionCost gradientCost t)≤
      T*E.bitPerRound model projectionCost gradientCost := by
  calc
    _ ≤ ∑ _t : Fin T,E.bitPerRound model projectionCost gradientCost :=
      Finset.sum_le_sum (fun t _=>E.bit_round_charge_le model projectionCost gradientCost t)
    _ = _ := by simp

/-- The list program, numerical work certificates, and complete rational
arithmetic charge refer to one actual trajectory. -/
theorem materialized_run_certificate (model : PolynomialArithmeticCharge)
    (projectionCost gradientCost : ℕ) :
    (∀ t≤T,((C.materializedRun 1 0 0 t).compactView ((standardRationalSchedule T K).live t)
      (rationalHistoryInitial C.initial_mean C.hi)).prediction=C.prediction t) ∧
    (∀ t<min T E.responseHorizon,∀ e,HistoryWorkHeights C.oracle (C.allCfg e) ((C.run t).histories e) C.lam
      (C.gradient t) (C.prediction t) E.uniformHistoryHeight) ∧
    (∀ t<min T E.responseHorizon,MasterWorkHeights C.master_precision ((standardRationalSchedule T K).live t)
      ((standardRationalSchedule T K).live (t+1)) (C.run t).weights
      (rationalSparseExponents C.lam (C.run t) (C.gradient t))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      E.uniformMasterHeight) ∧
    (∑ t : Fin T,E.bitRoundCharge model projectionCost gradientCost t)≤
      T*E.bitPerRound model projectionCost gradientCost := by
  exact ⟨C.materializedRun_prediction 1 0 0,fun t ht e=>E.uniform_history_work t (lt_min_iff.mp ht).2 e,
    fun t ht=>E.master_work_heights t (lt_min_iff.mp ht).1 (lt_min_iff.mp ht).2,
    E.total_bit_charge model projectionCost gradientCost⟩

end RationalRunEncodingSetup
end Paper254
#print axioms Paper254.RationalRunEncodingSetup.total_bit_charge
#print axioms Paper254.RationalRunEncodingSetup.materialized_run_certificate
