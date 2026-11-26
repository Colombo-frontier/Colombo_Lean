import RationalMaterializedRun254
import RationalExplicitOnline254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def materializedPoint (roundCost projectionCost gradientCost t : ℕ) (ht : t≤T) : W.carrier := by
  let w := ((C.materializedRun roundCost projectionCost gradientCost t).compactView
    ((standardRationalSchedule T K).live t) (rationalHistoryInitial C.initial_mean C.hi)).prediction
  refine ⟨WithLp.toLp 2 (fun j => (w j : ℝ)),?_⟩
  have hw : w=C.prediction t := C.materializedRun_prediction roundCost projectionCost gradientCost t ht
  rw [hw]
  exact C.prediction_feasible t

theorem materializedPoint_eq (roundCost projectionCost gradientCost t : ℕ) (ht : t≤T) :
    C.materializedPoint roundCost projectionCost gradientCost t ht=C.playedPoint t := by
  apply Subtype.ext
  change WithLp.toLp 2 (fun j => (((C.materializedRun roundCost projectionCost gradientCost t).compactView
    ((standardRationalSchedule T K).live t) (rationalHistoryInitial C.initial_mean C.hi)).prediction j : ℝ))=_
  rw [C.materializedRun_prediction roundCost projectionCost gradientCost t ht]
  rfl

def materializedLearner (roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle) : OnlineLearner W T :=
  fun t history => (C.forLosses oracle hspec (extendFinite (fun _ => 0) history)).materializedPoint
    roundCost projectionCost gradientCost t.val t.isLt.le

theorem materializedLearner_eq (roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle) :
    C.materializedLearner roundCost projectionCost gradientCost oracle hspec=C.onlineLearner oracle hspec := by
  funext t history
  exact (C.forLosses oracle hspec (extendFinite (fun _ => 0) history)).materializedPoint_eq
    roundCost projectionCost gradientCost t.val t.isLt.le

end RationalSparseConstruction

namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

/-- The list implementation, with the same deterministic working precision,
has exactly the dimension-sharp regret of the verified causal learner. -/
theorem materialized_regret_curved (hT : 0 < T) (roundCost projectionCost gradientCost : ℕ)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0 < delta) (hbudget : ((2 : ℝ)^I.s)⁻¹≤(I.lam : ℝ)*delta/(2*T))
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (u : Fin T → W.carrier)
    (hsmall : pathLength u≤curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2)) :
    regret (I.construction.materializedLearner roundCost projectionCost gradientCost oracle hspec) f u≤
      6144*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
        explicitCurvedRate (curvature D G eta) G d T (pathLength u))+delta := by
  rw [I.construction.materializedLearner_eq]
  exact I.regret_curved hT oracle hspec delta hdelta hbudget f hf hcompatible u hsmall

end ExplicitRationalSparseInput
end Paper254
#print axioms Paper254.RationalSparseConstruction.materializedLearner_eq
#print axioms Paper254.ExplicitRationalSparseInput.materialized_regret_curved
