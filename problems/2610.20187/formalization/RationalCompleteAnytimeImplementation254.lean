import RationalCompleteCertificate254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Joint anytime endpoint: every initialized epoch, only its executed responses,
actual cached trajectories, original-loss regret, routing and complete setup/round
primitive charges. The final partial epoch is charged only for its actual length. -/
theorem encoded_complete_anytime_implementation {d T : ℕ} (hd : 0<d) (hT : 0<T)
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
    (model integerModel : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ)
    (u : Fin T→W.carrier) (tau : ℝ) (htau : 0<tau) (hhi : tau≤(D:ℝ)) :
    let I := encodedRationalFamily hd D G H lam eta W hD hG heta hH hlam
      b z hDb hGb hHb hlb projection hprojection w0 hw0
    ∀ hgrad : ∀ j : Fin (epochCount T),∀ t<epochLength T j.val,
        RationalVectorBits ((rationalEpochConstruction I oracle hspec f j).gradient t) L0,
    let E : (j : Fin (epochCount T)) → RationalRunEncodingSetup (rationalEpochConstruction I oracle hspec f j) :=
      fun j => (I (2^j.val)).encodingSetup b L0 c degree (epochLength T j.val) (workingMagnitude_basic d (2^j.val) b).2.1
        hw0Bits hHb hlb hprojEncoding oracle hspec
        (extendFinite (fun _=>0) (paddedLoss (H := 2^j.val) (epochLoss f j))) (hgrad j)
    regret (anytimeRestriction (doublingLearner (rationalDoublingFamily I 1 0 0 oracle hspec)) T) f u≤
      2048*((epochCount T:ℝ)*(d+1:ℝ)*logFactor T^2/curvature (D:ℝ) (G:ℝ) eta+
        Real.sqrt (d+1:ℝ)*logFactor T^2/(curvature (D:ℝ) (G:ℝ) eta*tau)*pathLength u+
        curvature (D:ℝ) (G:ℝ) eta*(G:ℝ)^2*(2*T*tau^2+2*(D:ℝ)^2))+delta ∧
    (∀ j : Fin (epochCount T),CompleteImplementationCertificate (I (2^j.val)) oracle hspec
      (extendFinite (fun _=>0) (paddedLoss (H:=2^j.val) (epochLoss f j))) (E j) b (epochLength T j.val)
      model integerModel projectionCost gradientCost) ∧
    (∀ j : Fin (epochCount T),
      (countedPrecisionSetup d (2^j.val) b (z+j.val+1)).1.errorExponent=(I (2^j.val)).s) ∧
    anytimePrecisionCharge d T b z integerModel+
      completeAnytimeCharge E b model integerModel projectionCost gradientCost≤
      anytimePrecisionBound d T b z integerModel+doublingRouteBound T integerModel+
        epochCount T*completeAnytimeSetupBound (T:=T) (I:=I) b model integerModel+
        T*completeAnytimePerRound E model integerModel projectionCost gradientCost := by
  intro I hgrad E
  refine ⟨?_,?_,?_,?_⟩
  · exact encoded_rational_anytime hd D G H lam eta W hD hG heta hH hlam
      b z hDb hGb hHb hlb projection hprojection w0 hw0 1 0 0 oracle hspec delta hdelta
      T hT f hf hcompatible u tau htau hhi
  · intro j
    exact complete_implementation_certificate (I (2^j.val)) oracle hspec
      (extendFinite (fun _=>0) (paddedLoss (H:=2^j.val) (epochLoss f j))) (E j) b (epochLength T j.val)
      (min_le_left _ _) le_rfl hw0Bits hHb hlb model integerModel projectionCost gradientCost
  · intro j
    rw [countedPrecisionSetup_program]
    simp [I,encodedRationalFamily,encodedRationalSparseInput,Nat.log_pow]
  · simpa only [Nat.add_assoc] using Nat.add_le_add (anytime_precision_charge_le d T b z integerModel)
      (complete_anytime_charge E b model integerModel projectionCost gradientCost)
end Paper254
#print axioms Paper254.encoded_complete_anytime_implementation

