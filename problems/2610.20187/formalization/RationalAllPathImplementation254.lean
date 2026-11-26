import RationalImplementation254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- The clipped smoothing-scale objective, with the universal constant
made explicit. Its scale interval is exactly [D/T,D]. -/
def numericalClippedValue (d T : ℕ) (D G eta P : ℝ) : ℝ :=
  sInf (Set.range (fun tau : Set.Icc (D/T) D =>
    2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
      Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau.val)*P+
        curvature D G eta*G^2*T*tau.val^2)))

namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

theorem materialized_regret_all_paths (hT : 0<T)
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (delta : ℝ) (hdelta : 0<delta) (hbudget : ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T))
    (f : Fin T→Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t,RationalLossCompatible W oracle (f t)) (u : Fin T→W.carrier) :
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      min (G*D*T) (numericalClippedValue d T D G eta (pathLength u)+delta) := by
  rw [I.construction.materializedLearner_eq]
  apply le_min
  · exact linear_regret_bound _ f u I.gradient_pos.le hf
  · have hTone : (1:ℝ)≤T := by exact_mod_cast hT
    have hscale : D/T≤D := div_le_self I.diameter_pos.le hTone
    have hne : (Set.range (fun tau : Set.Icc (D/T) D =>
        2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
          Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau.val)*pathLength u+
            curvature D G eta*G^2*T*tau.val^2))).Nonempty :=
      ⟨_,⟨⟨D,hscale,le_rfl⟩,rfl⟩⟩
    have hlower : regret (I.learner oracle hspec) f u-delta≤
        numericalClippedValue d T D G eta (pathLength u) := by
      apply le_csInf hne
      rintro _ ⟨tau,rfl⟩
      have hh := I.regret_clipped hT oracle hspec delta hdelta hbudget f hf hcompatible u
        tau.val tau.property.1 tau.property.2
      linarith
    change regret (I.learner oracle hspec) f u≤_
    linarith

end ExplicitRationalSparseInput

/-- All comparator paths, clipped scale optimization, and the linear cap
are certified jointly with the actual finite-horizon program's bit charge.
Only the T executed gradient responses require encoding bounds. -/
theorem encoded_all_path_implementation {d T : ℕ} (hd : 0<d) (hT : 0<T)
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
    (model : PolynomialArithmeticCharge) (projectionCost gradientCost : ℕ) (u : Fin T→W.carrier) :
    let I := encodedRationalSparseInput (T:=T) hd D G H lam eta W hD hG heta hH hlam
      b z hDb hGb hHb hlb projection hprojection w0 hw0
    ∀ hgrad : ∀ t<T,RationalVectorBits
        ((I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)).gradient t) L0,
    let E := I.encodingSetup b L0 c degree T (workingMagnitude_basic d T b).2.1
      hw0Bits hHb hlb hprojEncoding oracle hspec (extendFinite (fun _=>0) f) hgrad
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      min ((G:ℝ)*(D:ℝ)*T) (numericalClippedValue d T (D:ℝ) (G:ℝ) eta (pathLength u)+delta) ∧
    (∑ t : Fin T,E.bitRoundCharge model projectionCost gradientCost t)≤
      T*E.bitPerRound model projectionCost gradientCost := by
  intro I hgrad E
  have hpos : 0<delta := lt_of_lt_of_le (by positivity : 0<((2:ℝ)^z)⁻¹) hdelta
  have hb := encodedRationalSparseInput_budget hd hT D G H lam eta W hD hG heta hH hlam
    b z hDb hGb hHb hlb projection hprojection w0 hw0 delta hdelta
  exact ⟨I.materialized_regret_all_paths hT oracle hspec delta hpos hb f hf hcompatible u,
    E.total_bit_charge model projectionCost gradientCost⟩

end Paper254
#print axioms Paper254.ExplicitRationalSparseInput.materialized_regret_all_paths
#print axioms Paper254.encoded_all_path_implementation
