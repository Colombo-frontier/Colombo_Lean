import RationalEncodedAnytime254
import RationalAnytimeCost254
import RationalExplicitEncoding254

noncomputable section
namespace Paper254

/-- Original-loss regret and the executed-epoch bit charge for the same
explicitly tuned anytime program. Only initial encodings and actual oracle
response encodings enter; no history potential or evolved-state bound is
assumed. -/
theorem encoded_anytime_implementation {d T : ℕ} (hd : 0<d) (hT : 0<T)
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
    rationalAnytimeBitCharge E model projectionCost gradientCost≤
      T*rationalAnytimePerRound E model projectionCost gradientCost := by
  intro I hgrad E
  constructor
  · exact encoded_rational_anytime hd D G H lam eta W hD hG heta hH hlam
      b z hDb hGb hHb hlb projection hprojection w0 hw0 1 0 0 oracle hspec delta hdelta
      T hT f hf hcompatible u tau htau hhi
  · exact rational_anytime_bit_charge E model projectionCost gradientCost

end Paper254
#print axioms Paper254.encoded_anytime_implementation
