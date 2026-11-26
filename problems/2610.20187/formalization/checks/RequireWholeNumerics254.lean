import RationalImplementation254
import RationalAllPathImplementation254
import RationalAnytimeImplementation254
import FrontierImplementation254
import RationalAnytimeCost254
import NumericalTolerance254
import HistoryWorkspace254
import BoundedRationalOracle254
import RationalCompleteImplementation254
import RationalCompleteAnytimeImplementation254
import RationalRawCompleteImplementation254
import RationalRawCompleteAnytime254

noncomputable section
open Paper254
open scoped BigOperators

/-- Original-loss regret for every path and the same initialized program's
complete modeled charge; only the actual T oracle responses are required. -/
example {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W) (hT : 0<T)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0<delta) (hbudget : ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T))
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t)) (u : Fin T→W.carrier)
    (E : RationalRunEncodingSetup (I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)))
    (hresponse : T≤E.responseHorizon) (b : ℕ)
    (hmean : RationalVectorBits I.initial_mean b) (hhi : RationalHeight I.hi b)
    (hlam : RationalHeight I.lam b)
    (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      min (G*D*T) (numericalClippedValue d T D G eta (pathLength u)+delta) ∧
    CompleteImplementationCertificate I oracle hspec (extendFinite (fun _=>0) f) E b T
      rationalModel integerModel projectionCost gradientCost := by
  exact ⟨I.materialized_regret_all_paths hT oracle hspec delta hdelta hbudget f hf hcompatible u,
    complete_implementation_certificate I oracle hspec (extendFinite (fun _=>0) f) E b T
      le_rfl hresponse hmean hhi hlam rationalModel integerModel projectionCost gradientCost⟩

/-- Independently typed all-budget target for the actual list learner. -/
example {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W) (hT : 0<T)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0<delta) (hbudget : ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T))
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t)) (u : Fin T→W.carrier)
    (tau : ℝ) (htau : D/T≤tau) (htauMax : tau≤D) :
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      min (2048*((d+1:ℝ)*logFactor T^2/curvature D G eta+
        Real.sqrt (d+1:ℝ)*logFactor T^2/(curvature D G eta*tau)*pathLength u+
          curvature D G eta*G^2*T*tau^2)+delta) (G*D*T) := by
  apply le_min
  · rw [I.construction.materializedLearner_eq]
    exact I.regret_clipped hT oracle hspec delta hdelta hbudget f hf hcompatible u tau htau htauMax
  · exact linear_regret_bound _ f u I.gradient_pos.le hf

/-- The encoding record has only initial input, parameter and actual
oracle-output contracts, not assumptions about evolved algorithm states. -/
example {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
    (C : RationalSparseConstruction d T K D G eta W) (E : RationalRunEncodingSetup C)
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    (∑ t : Fin T,E.bitRoundCharge model projectionCost gradientCost t)≤
      T*E.bitPerRound model projectionCost gradientCost := E.total_bit_charge model projectionCost gradientCost

example {d : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :
    (profiledHistoryStep roundCost projectionCost projectionWorkspace oracle cfg S lam g w).1=
      countedHistoryStep roundCost projectionCost oracle cfg S lam g w ∧
    (profiledHistoryStep roundCost projectionCost projectionWorkspace oracle cfg S lam g w).2≤
      60*(d+1)^2+projectionWorkspace :=
  ⟨profiledHistoryStep_program _ _ _ _ _ _ _ _ _,profiledHistoryStep_workspace _ _ _ _ _ _ _ _ _⟩

#print axioms Paper254.encoded_implementation_certificate
#print axioms Paper254.encoded_all_path_implementation
#print axioms Paper254.encoded_anytime_implementation
#print axioms Paper254.implementedFrontier_regret
#print axioms Paper254.implementedFrontier_prediction
#print axioms Paper254.implementedFrontier_total_overhead
#print axioms Paper254.RationalRunEncodingSetup.materialized_run_certificate
#print axioms Paper254.RationalRunEncodingSetup.master_run_certificate
#print axioms Paper254.RationalRunEncodingSetup.history_work_heights
#print axioms Paper254.RationalSparseConstruction.materializedRun_refines
#print axioms Paper254.profiledHistoryStep_program
#print axioms Paper254.profiledHistoryStep_workspace
#print axioms Paper254.rationalToleranceExponent_spec
#print axioms Paper254.rational_anytime_bit_charge
#print axioms Paper254.rational_anytime_gradient_queries
#print axioms Paper254.encoded_complete_all_path_implementation
#print axioms Paper254.complete_implementation_certificate
#print axioms Paper254.encoded_complete_anytime_implementation
#print axioms Paper254.raw_encoded_complete_all_path_implementation
#print axioms Paper254.raw_encoded_complete_anytime_implementation

#eval decide (Paper254.rationalToleranceExponent (1/1000) (by norm_num)=10)
#eval decide ((Paper254.countedGeneralInverse (fun i j : Fin 2=>if i=j then (2:ℚ) else 1)).1=
  (fun i j : Fin 2=>if i=j then (2/3:ℚ) else -(1/3:ℚ)))
