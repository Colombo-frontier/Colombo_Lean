import RationalRawCompleteImplementation254
import RationalCompleteAnytimeImplementation254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- A single raw rational regularity preprocessing is shared by every
epoch. Setup, routing and only the executed round prefixes are charged. -/
theorem raw_encoded_complete_anytime_implementation {d T : ℕ} (hd : 0<d) (hT : 0<T)
    (D G eta : ℚ) (W : Domain d (D:ℝ))
    (hD : 0<(D:ℝ)) (hG : 0<(G:ℝ)) (heta : 0<(eta:ℝ))
    (b z L0 c degree : ℕ) (hDb : RationalHeight D b) (hGb : RationalHeight G b)
    (hetab : RationalHeight eta b)
    (projection : RationalProjectionProcedure d) (hprojection : RationalProjectionSpec W projection)
    (hprojEncoding : ProjectionEncodingSpec projection L0 c degree)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (hw0Bits : RationalVectorBits w0 b)
    (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W (G:ℝ) (eta:ℝ) oracle)
    (delta : ℝ) (hdelta : ((2:ℝ)^z)⁻¹≤delta)
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W (G:ℝ) (eta:ℝ) (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t))
    (model integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ)
    (u : Fin T→W.carrier) (tau : ℝ) (htau : 0<tau) (hhi : tau≤(D:ℝ)) :
    let B := 2*b+6
    let I := encodedRationalFamily hd D G (rationalDiameterSquare D)
      (rationalLearningRate D G eta) (eta:ℝ) W hD hG heta (rationalDiameterSquare_cast D)
      (rationalLearningRate_cast D G eta) B z (hDb.mono (by omega)) (hGb.mono (by omega))
      ((rationalDiameterSquare_height D b hDb).mono (by omega))
      (rationalLearningRate_height D G eta b hDb hGb hetab) projection hprojection w0 hw0
    ∀ hgrad : ∀ j : Fin (epochCount T),∀ t<epochLength T j.val,
        RationalVectorBits ((rationalEpochConstruction I oracle hspec f j).gradient t) L0,
    let E : (j : Fin (epochCount T)) → RationalRunEncodingSetup (rationalEpochConstruction I oracle hspec f j) :=
      fun j => (I (2^j.val)).encodingSetup B L0 c degree (epochLength T j.val)
        (workingMagnitude_basic d (2^j.val) B).2.1 (hw0Bits.mono (by omega))
        ((rationalDiameterSquare_height D b hDb).mono (by omega))
        (rationalLearningRate_height D G eta b hDb hGb hetab) hprojEncoding oracle hspec
        (extendFinite (fun _=>0) (paddedLoss (H := 2^j.val) (epochLoss f j))) (hgrad j)
    regret (anytimeRestriction (doublingLearner (rationalDoublingFamily I 1 0 0 oracle hspec)) T) f u≤
      2048*((epochCount T:ℝ)*(d+1:ℝ)*logFactor T^2/curvature (D:ℝ) (G:ℝ) (eta:ℝ)+
        Real.sqrt (d+1:ℝ)*logFactor T^2/(curvature (D:ℝ) (G:ℝ) (eta:ℝ)*tau)*pathLength u+
        curvature (D:ℝ) (G:ℝ) (eta:ℝ)*(G:ℝ)^2*(2*T*tau^2+2*(D:ℝ)^2))+delta ∧
    (∀ j : Fin (epochCount T),CompleteImplementationCertificate (I (2^j.val)) oracle hspec
      (extendFinite (fun _=>0) (paddedLoss (H:=2^j.val) (epochLoss f j))) (E j) B (epochLength T j.val)
      model integerModel projectionCost gradientCost) ∧
    (∀ j : Fin (epochCount T),
      (countedPrecisionSetup d (2^j.val) B (z+j.val+1)).1.errorExponent=(I (2^j.val)).s) ∧
    regularityCharge D G eta b model+anytimePrecisionCharge d T B z integerModel+
      completeAnytimeCharge E B model integerModel projectionCost gradientCost≤
      regularityChargeBound b model+anytimePrecisionBound d T B z integerModel+
        doublingRouteBound T integerModel+
        epochCount T*completeAnytimeSetupBound (T:=T) (I:=I) B model integerModel+
        T*completeAnytimePerRound E model integerModel projectionCost gradientCost := by
  intro B I hgrad E
  have hh := encoded_complete_anytime_implementation hd hT D G (rationalDiameterSquare D)
    (rationalLearningRate D G eta) (eta:ℝ) W hD hG heta (rationalDiameterSquare_cast D)
    (rationalLearningRate_cast D G eta) B z L0 c degree
    (hDb.mono (by dsimp [B]; omega)) (hGb.mono (by dsimp [B]; omega))
    ((rationalDiameterSquare_height D b hDb).mono (by dsimp [B]; omega))
    (rationalLearningRate_height D G eta b hDb hGb hetab)
    projection hprojection hprojEncoding w0 hw0 (hw0Bits.mono (by dsimp [B]; omega))
    oracle hspec delta hdelta f hf hcompatible model integerModel projectionCost gradientCost
    u tau htau hhi hgrad
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  simpa only [Nat.add_assoc] using
    Nat.add_le_add (regularity_charge_le D G eta b model) hh.2.2.2

end Paper254
#print axioms Paper254.raw_encoded_complete_anytime_implementation
