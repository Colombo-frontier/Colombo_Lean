import ExactTotalCost254
import ExactWorkspace254
import ExactProjectionInterface254
import FrontierImplementation254
import FullyScheduledTransition254
import RationalRoundWorkspace254
import RationalCompleteImplementation254
import CachedRuntimeWorkspace254

noncomputable section
open Paper254
open scoped BigOperators

/-- The initialized cached program and its setup-plus-prefix cost must be
certified from initial inputs and actual oracle responses. -/
example {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : ExplicitRationalSparseInput d T D G eta W)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ→Loss d) (E : RationalRunEncodingSetup (I.construction.forLosses oracle hspec f))
    (b R : ℕ) (hRT : R≤T) (hresponse : R≤E.responseHorizon)
    (hmean : RationalVectorBits I.initial_mean b) (hhi : RationalHeight I.hi b)
    (hlam : RationalHeight I.lam b)
    (rationalModel integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) :
    (∀ t,preparedRun I.preparation.1.1 (I.construction.forLosses oracle hspec f).master_precision
      (I.construction.forLosses oracle hspec f).oracle (I.construction.forLosses oracle hspec f).lam
      (I.construction.forLosses oracle hspec f).query t=
        (I.construction.forLosses oracle hspec f).materializedRun 1 0 0 t) ∧
    completeImplementationCharge I E b R rationalModel integerModel projectionCost gradientCost≤
      I.preparationBound b rationalModel integerModel+
        R*E.completePerRound rationalModel integerModel projectionCost gradientCost := by
  have h := complete_implementation_certificate I oracle hspec f E b R hRT hresponse
    hmean hhi hlam rationalModel integerModel projectionCost gradientCost
  exact ⟨h.actual_run,h.total_charge⟩

example {d : ℕ} (hd : 0<d) {D : ℝ} {W : Domain d D}
    (spectral : ExactSpectralPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (c : ℕ) (hc : spectral.bound≤c*d^3) :
    exactRoundArithmeticBound (denseRankOneFloorPrimitive spectral) projection exponential≤
      (c+44)*d^3+projection.bound+exponential.bound :=
  exact_dense_arithmetic_bound hd spectral projection exponential c hc

example {d : ℕ} (hd : 0<d) {D : ℝ} {W : Domain d D}
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (c : ℕ) (hc : primitive.bound≤c*d^2) :
    exactRoundArithmeticBound primitive projection exponential≤
      (c+36)*d^2+projection.bound+exponential.bound :=
  exact_quadratic_arithmetic_bound hd primitive projection exponential c hc

example {d : ℕ} (T K t : ℕ) (S : MaterializedRationalSparseData d ((T+1)*(K+1)))
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters) (prior : Fin ((T+1)*(K+1))→ℚ×ℕ)
    (alpha lam : ℚ) (initial : RationalHistoryData d) (query : RationalGradientQuery d) :
    (fullyScheduledMaterializedStep T K t S p roundCost projectionCost gradientCost
      oracle cfg prior alpha lam initial query).1=
      S.step p roundCost projectionCost gradientCost oracle cfg
        ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
        (fun e=>(prior e).1) alpha lam initial query :=
  fullyScheduledMaterializedStep_program T K t S p roundCost projectionCost gradientCost
    oracle cfg prior alpha lam initial query

#print axioms Paper254.rotatedPrecision_map_eq
#print axioms Paper254.countedExactHistory_value
#print axioms Paper254.countedExactRound_weights
#print axioms Paper254.countedExactRound_histories
#print axioms Paper254.exact_curved_total_cost
#print axioms Paper254.exact_dense_arithmetic_bound
#print axioms Paper254.exact_quadratic_arithmetic_bound
#print axioms Paper254.implementedFrontier_prediction
#print axioms Paper254.implementedFrontier_regret
#print axioms Paper254.implementedFrontier_total_overhead
#print axioms Paper254.fullyScheduledMaterializedStep_program
#print axioms Paper254.fullyScheduled_total_metadata
#print axioms Paper254.profiledRationalRound_program
#print axioms Paper254.profiledRationalRound_workspace
#print axioms Paper254.RationalSparseConstruction.materialized_workspace_bound
#print axioms Paper254.exactSparseOwnedCells_bound
#print axioms Paper254.countedPrecisionSetup_program
#print axioms Paper254.precision_setup_arithmetic_operand_bits
#print axioms Paper254.precision_setup_log_operand_bits
#print axioms Paper254.complete_implementation_certificate
#print axioms Paper254.encoded_complete_all_path_implementation
#print axioms Paper254.cached_integer_component_bits
#print axioms Paper254.profiledPreparedStep_program
#print axioms Paper254.profiledPreparedStep_workspace
#print axioms Paper254.RationalSparseConstruction.prepared_run_owned_cells
#print axioms Paper254.RationalSparseConstruction.prepared_run_owned_bit_budget

#eval ([0,1,31,1000,1200] : List ℕ).all (fun t=>decide
  ((fullyCountedStandardLive 1000 9 t).1=((standardRationalSchedule 1000 9).live t).sort (·≤·)))
#eval decide ((fullyCountedStandardLive 1000 9 31).2≤
  shortMetadataBound (Nat.log 2 (1000+1)+1) 9+3*Nat.log 2 (1000+1)+4)
