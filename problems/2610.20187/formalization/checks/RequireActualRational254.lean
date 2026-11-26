import RationalEncodedInput254
import RationalMasterEncoding254
import RationalPredictionHeight254
import RationalEncodingReset254
import EfficientHistoryCost254
import SparseHistoryCost254

noncomputable section
open Paper254

/-- Independent target: the actual causal learner, original losses and
Euclidean comparator path, with an explicit numerical budget. -/
example {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W) (hT : 0<T)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0<delta) (hbudget : ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T))
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t)) (u : Fin T→W.carrier)
    (tau : ℝ) (htau : D/T≤tau) (htauMax : tau≤D) :
    regret (I.learner oracle hspec) f u≤2048*((d+1:ℝ)*logFactor T^2/curvature D G eta+
      Real.sqrt (d+1:ℝ)*logFactor T^2/(curvature D G eta*tau)*pathLength u+
      curvature D G eta*G^2*T*tau^2)+delta :=
  I.regret_clipped hT oracle hspec delta hdelta hbudget f hf hcompatible u tau htau htauMax

example {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W) (hT : 0<T)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0<delta) (hbudget : ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T))
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t)) (u : Fin T→W.carrier)
    (hsmall : pathLength u≤curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1:ℝ)*logFactor T^2)) :
    regret (I.learner oracle hspec) f u≤6144*((d+1:ℝ)*logFactor T^2/curvature D G eta+
      explicitCurvedRate (curvature D G eta) G d T (pathLength u))+delta :=
  I.regret_curved hT oracle hspec delta hdelta hbudget f hf hcompatible u hsmall

#print axioms Paper254.ExplicitRationalSparseInput.regret_clipped
#print axioms Paper254.ExplicitRationalSparseInput.regret_curved
#print axioms Paper254.encodedRationalSparseInput_budget
#print axioms Paper254.explicit_history_precision_and_guards
#print axioms Paper254.rationalMasterUpdate_reduced_bits
#print axioms Paper254.rationalSparsePrediction_bits
#print axioms Paper254.rationalExponent_height
#print axioms Paper254.rationalExp_reduced_bits
#print axioms Paper254.rationalHistoryStep_stored_bits
#print axioms Paper254.countedHistoryStep_value
#print axioms Paper254.countedHistoryStep_cost
