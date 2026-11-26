import RationalExplicitEncoding254
import RationalRunBitCost254
import RationalMaterializedOnline254
import RationalEncodedInput254

noncomputable section
open scoped BigOperators
namespace Paper254
namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

/-- Original-loss regret and whole-run arithmetic/bit charging for one
actual list learner. Encoding assumptions concern only input parameters,
the initial point, and actual oracle responses. -/
theorem implementation_certificate (hT : 0<T)
    (b L0 c degree : ℕ) (hbv : b≤I.v)
    (hmean : RationalVectorBits I.initial_mean b)
    (hhi : RationalHeight I.hi b) (hlam : RationalHeight I.lam b)
    (hproj : ProjectionEncodingSpec I.oracle L0 c degree)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0<delta) (hbudget : ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T))
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t))
    (hgrad : ∀ t<T,RationalVectorBits
      ((I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)).gradient t) L0)
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ)
    (u : Fin T→W.carrier)
    (hsmall : pathLength u≤curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1:ℝ)*logFactor T^2)) :
    let C := I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)
    let E := I.encodingSetup b L0 c degree T hbv hmean hhi hlam hproj oracle hspec
      (extendFinite (fun _=>0) f) hgrad
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      6144*((d+1:ℝ)*logFactor T^2/curvature D G eta+
        explicitCurvedRate (curvature D G eta) G d T (pathLength u))+delta ∧
    (∑ t : Fin T,E.bitRoundCharge model projectionCost gradientCost t)≤
      T*E.bitPerRound model projectionCost gradientCost ∧
    (∀ t<T,∀ e,HistoryWorkHeights C.oracle (C.allCfg e) ((C.run t).histories e) C.lam
      (C.gradient t) (C.prediction t) E.uniformHistoryHeight) ∧
    (∀ t≤T,((C.materializedRun 1 0 0 t).compactView ((standardRationalSchedule T (scaleCount T)).live t)
      (rationalHistoryInitial C.initial_mean C.hi)).prediction=C.prediction t) := by
  dsimp only
  let E := I.encodingSetup b L0 c degree T hbv hmean hhi hlam hproj oracle hspec
    (extendFinite (fun _=>0) f) hgrad
  exact ⟨I.materialized_regret_curved hT 1 0 0 oracle hspec delta hdelta hbudget f hf hcompatible u hsmall,
    E.total_bit_charge model projectionCost gradientCost,fun t ht e=>E.uniform_history_work t ht e,
    (E.materialized_run_certificate model projectionCost gradientCost).1⟩

/-- The scale sum has only log T terms and every summand has the same
explicit polynomial numerical precision. It never ranges over T births. -/
theorem encoding_uniform_history_height (b L0 c degree responseHorizon : ℕ) (hbv : b≤I.v)
    (hmean : RationalVectorBits I.initial_mean b)
    (hhi : RationalHeight I.hi b) (hlam : RationalHeight I.lam b)
    (hproj : ProjectionEncodingSpec I.oracle L0 c degree)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : ℕ→Loss d)
    (hgrad : ∀ t<responseHorizon,RationalVectorBits ((I.construction.forLosses oracle hspec f).gradient t) L0) :
    let C := I.construction.forLosses oracle hspec f
    let E := I.encodingSetup b L0 c degree responseHorizon hbv hmean hhi hlam hproj oracle hspec f hgrad
    E.uniformHistoryHeight=(scaleCount T+1)*
      historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree (C.cfg 0) := by
  dsimp only
  let E := I.encodingSetup b L0 c degree responseHorizon hbv hmean hhi hlam hproj oracle hspec f hgrad
  change (∑ j : Fin (scaleCount T+1),historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree
    ((I.construction.forLosses oracle hspec f).cfg j))=(scaleCount T+1)*
      historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree
        ((I.construction.forLosses oracle hspec f).cfg 0)
  calc
    _ = ∑ _j : Fin (scaleCount T+1),historyWorkHeight d E.inputHeight E.v E.L0 E.c E.degree
        ((I.construction.forLosses oracle hspec f).cfg 0) := Finset.sum_congr rfl (by intro j _; rfl)
    _ = _ := by simp

end ExplicitRationalSparseInput

/-- End-to-end numerical specialization with polynomially selected
precision from rational input encodings. No local error or state-height
claim is supplied as a hypothesis. Oracle responses retain their explicit
input-size contract, as in the manuscript's rational-oracle model. -/
theorem encoded_implementation_certificate {d T : ℕ} (hd : 0<d) (hT : 0<T)
    (D G H lam : ℚ) (eta : ℝ) (W : Domain d (D:ℝ))
    (hD : 0<(D:ℝ)) (hG : 0<(G:ℝ)) (heta : 0<eta)
    (hH : (H:ℝ)=(D:ℝ)^2) (hlam : 2*(lam:ℝ)=curvature (D:ℝ) (G:ℝ) eta)
    (b z L0 c degree : ℕ) (hDb : RationalHeight D b) (hGb : RationalHeight G b)
    (hHb : RationalHeight H b) (hlb : RationalHeight lam b)
    (projection : RationalProjectionProcedure d) (hprojection : RationalProjectionSpec W projection)
    (hprojEncoding : ProjectionEncodingSpec projection L0 c degree)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (hw0Bits : RationalVectorBits w0 b)
    (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W (G:ℝ) eta oracle)
    (delta : ℝ) (hdelta : ((2:ℝ)^z)⁻¹≤delta)
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W (G:ℝ) eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t))
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ)
    (u : Fin T→W.carrier)
    (hsmall : pathLength u≤curvature (D:ℝ) (G:ℝ) eta^2*(G:ℝ)^2*T*(D:ℝ)^3/
      (Real.sqrt (d+1:ℝ)*logFactor T^2)) :
    let I := encodedRationalSparseInput (T:=T) hd D G H lam eta W hD hG heta hH hlam
      b z hDb hGb hHb hlb projection hprojection w0 hw0
    ∀ hgrad : ∀ t<T,RationalVectorBits
        ((I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)).gradient t) L0,
    let E := I.encodingSetup b L0 c degree T (workingMagnitude_basic d T b).2.1
      hw0Bits hHb hlb hprojEncoding oracle hspec (extendFinite (fun _=>0) f) hgrad
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      6144*((d+1:ℝ)*logFactor T^2/curvature (D:ℝ) (G:ℝ) eta+
        explicitCurvedRate (curvature (D:ℝ) (G:ℝ) eta) (G:ℝ) d T (pathLength u))+delta ∧
    (∑ t : Fin T,E.bitRoundCharge model projectionCost gradientCost t)≤
      T*E.bitPerRound model projectionCost gradientCost := by
  dsimp only
  intro hgrad
  let I := encodedRationalSparseInput (T:=T) hd D G H lam eta W hD hG heta hH hlam
    b z hDb hGb hHb hlb projection hprojection w0 hw0
  have hpos : 0<delta := lt_of_lt_of_le (by positivity : 0<((2:ℝ)^z)⁻¹) hdelta
  have hb := encodedRationalSparseInput_budget hd hT D G H lam eta W hD hG heta hH hlam
    b z hDb hGb hHb hlb projection hprojection w0 hw0 delta hdelta
  have cert := I.implementation_certificate hT b L0 c degree (workingMagnitude_basic d T b).2.1
    hw0Bits hHb hlb hprojEncoding oracle hspec delta hpos hb f hf hcompatible hgrad model
    projectionCost gradientCost u hsmall
  exact ⟨cert.1,cert.2.1⟩

end Paper254
#print axioms Paper254.ExplicitRationalSparseInput.implementation_certificate
#print axioms Paper254.ExplicitRationalSparseInput.encoding_uniform_history_height
#print axioms Paper254.encoded_implementation_certificate
