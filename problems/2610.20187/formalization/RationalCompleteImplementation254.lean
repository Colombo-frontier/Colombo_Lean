import RationalCompleteCertificate254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Original inputs produce one fully initialized trajectory: original-loss regret,
actual response encoding, setup widths, exact cached execution and all modeled
setup/round charges are certified together. The precision exponent z is input. -/
theorem encoded_complete_all_path_implementation {d T : ℕ} (hd : 0<d) (hT : 0<T)
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
    (model integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) (u : Fin T→W.carrier) :
    let I := encodedRationalSparseInput (T:=T) hd D G H lam eta W hD hG heta hH hlam
      b z hDb hGb hHb hlb projection hprojection w0 hw0
    ∀ hgrad : ∀ t<T,RationalVectorBits
        ((I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)).gradient t) L0,
    let E := I.encodingSetup b L0 c degree T (workingMagnitude_basic d T b).2.1
      hw0Bits hHb hlb hprojEncoding oracle hspec (extendFinite (fun _=>0) f) hgrad
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      min ((G:ℝ)*(D:ℝ)*T) (numericalClippedValue d T (D:ℝ) (G:ℝ) eta (pathLength u)+delta) ∧
    CompleteImplementationCertificate I oracle hspec (extendFinite (fun _=>0) f) E b T
      model integerModel projectionCost gradientCost ∧
    (countedPrecisionSetup d T b z).1.magnitude=I.v ∧
    (countedPrecisionSetup d T b z).1.errorExponent=I.s ∧
    precisionCharge d T b z integerModel+
      completeImplementationCharge I E b T model integerModel projectionCost gradientCost≤
      precisionChargeBound d T b z integerModel+I.preparationBound b model integerModel+
        T*E.completePerRound model integerModel projectionCost gradientCost := by
  intro I hgrad E
  have hpos : 0<delta := lt_of_lt_of_le (by positivity : 0<((2:ℝ)^z)⁻¹) hdelta
  have hb := encodedRationalSparseInput_budget hd hT D G H lam eta W hD hG heta hH hlam
    b z hDb hGb hHb hlb projection hprojection w0 hw0 delta hdelta
  refine ⟨I.materialized_regret_all_paths hT oracle hspec delta hpos hb f hf hcompatible u,
    complete_implementation_certificate I oracle hspec (extendFinite (fun _=>0) f) E b T
      le_rfl le_rfl hw0Bits hHb hlb model integerModel projectionCost gradientCost,?_,?_,?_⟩
  · rw [countedPrecisionSetup_program]
    rfl
  · rw [countedPrecisionSetup_program]
    rfl
  · simpa only [Nat.add_assoc] using Nat.add_le_add (precision_charge_le d T b z integerModel)
      (complete_implementation_charge I E b T model integerModel projectionCost gradientCost)
end Paper254
#print axioms Paper254.encoded_complete_all_path_implementation

