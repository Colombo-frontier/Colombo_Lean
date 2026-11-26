import RationalCompleteImplementation254
import RationalRegularity254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- All rational intermediates in the regularity constructor have a
linear encoding bound, including both operands of its comparison. -/
theorem rationalRegularity_work_heights (D G eta : ℚ) (b : ℕ)
    (hD : RationalHeight D b) (hG : RationalHeight G b) (heta : RationalHeight eta b) :
    ∀ q∈[D,G,eta,D*D,eta/2,4*G,4*G*D,1/(4*G*D),
      rationalCurvature D G eta,rationalLearningRate D G eta],
      RationalHeight q (2*b+6) := by
  have h4 : RationalHeight (4:ℚ) 2 := by
    simpa using RationalHeight.of_int 4 2 (by norm_num)
  have hleft : RationalHeight (eta/2) (2*b+6) := by
    have hh := heta.mul rational_half_height
    rw [mul_one_div] at hh
    exact hh.mono (by omega)
  have hfour : RationalHeight (4*G) (2*b+6) :=
    (h4.mul hG).mono (by omega)
  have hden : RationalHeight (4*G*D) (2*b+4) := by
    simpa only [show 2+b+1+b+1=2*b+4 by omega] using (h4.mul hG).mul hD
  have hinv : RationalHeight (1/(4*G*D)) (2*b+6) := by
    simpa only [one_div] using hden.inv.mono (show 2*b+4≤2*b+6 by omega)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hD.mono (by omega)
  · exact hG.mono (by omega)
  · exact heta.mono (by omega)
  · exact (hD.mul hD).mono (by omega)
  · exact hleft
  · exact hfour
  · exact hden.mono (by omega)
  · exact hinv
  · exact (rationalCurvature_height D G eta b hD hG heta).mono (by omega)
  · exact rationalLearningRate_height D G eta b hD hG heta

/-- Six arithmetic primitives and one rational comparison. -/
def regularityCharge (D G eta : ℚ) (b : ℕ) (model : PolynomialArithmeticCharge) : ℕ :=
  ((countedRationalRegularity D G eta).2.1+(countedRationalRegularity D G eta).2.2)*
    model.cost (2*b+6)

def regularityChargeBound (b : ℕ) (model : PolynomialArithmeticCharge) : ℕ :=
  7*model.coefficient*(2*b+7)^model.degree

theorem regularity_charge_le (D G eta : ℚ) (b : ℕ) (model : PolynomialArithmeticCharge) :
    regularityCharge D G eta b model≤regularityChargeBound b model := by
  have hh := Nat.mul_le_mul_left 7 (model.bound (2*b+6))
  simpa only [regularityCharge,countedRationalRegularity_cost,regularityChargeBound,
    show 6+1=(7:ℕ) by norm_num,show 2*b+6+1=2*b+7 by omega,Nat.mul_assoc] using hh

/-- The raw rational diameter, gradient and exp-concavity parameters
construct H and lambda, all integer precisions and the cached learner.
The complete modeled charge includes that initial construction. -/
theorem raw_encoded_complete_all_path_implementation {d T : ℕ} (hd : 0<d) (hT : 0<T)
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
    (u : Fin T→W.carrier) :
    let B := 2*b+6
    let I := encodedRationalInputFromRegularity (T:=T) hd D G eta W hD hG heta b z
      hDb hGb hetab projection hprojection w0 hw0
    ∀ hgrad : ∀ t<T,RationalVectorBits
        ((I.construction.forLosses oracle hspec (extendFinite (fun _=>0) f)).gradient t) L0,
    let E := I.encodingSetup B L0 c degree T (workingMagnitude_basic d T B).2.1
      (hw0Bits.mono (by omega)) ((rationalDiameterSquare_height D b hDb).mono (by omega))
      (rationalLearningRate_height D G eta b hDb hGb hetab) hprojEncoding oracle hspec
      (extendFinite (fun _=>0) f) hgrad
    regret (I.construction.materializedLearner 1 0 0 oracle hspec) f u≤
      min ((G:ℝ)*(D:ℝ)*T) (numericalClippedValue d T (D:ℝ) (G:ℝ) (eta:ℝ) (pathLength u)+delta) ∧
    CompleteImplementationCertificate I oracle hspec (extendFinite (fun _=>0) f) E B T
      model integerModel projectionCost gradientCost ∧
    (countedRationalRegularity D G eta).1=(I.hi,I.lam) ∧
    (countedPrecisionSetup d T B z).1.magnitude=I.v ∧
    (countedPrecisionSetup d T B z).1.errorExponent=I.s ∧
    regularityCharge D G eta b model+precisionCharge d T B z integerModel+
      completeImplementationCharge I E B T model integerModel projectionCost gradientCost≤
      regularityChargeBound b model+precisionChargeBound d T B z integerModel+
        I.preparationBound B model integerModel+
        T*E.completePerRound model integerModel projectionCost gradientCost := by
  intro B I hgrad E
  have hh := encoded_complete_all_path_implementation hd hT D G (rationalDiameterSquare D)
    (rationalLearningRate D G eta) (eta:ℝ) W hD hG heta (rationalDiameterSquare_cast D)
    (rationalLearningRate_cast D G eta) B z L0 c degree
    (hDb.mono (by dsimp [B]; omega)) (hGb.mono (by dsimp [B]; omega))
    ((rationalDiameterSquare_height D b hDb).mono (by dsimp [B]; omega))
    (rationalLearningRate_height D G eta b hDb hGb hetab)
    projection hprojection hprojEncoding w0 hw0 (hw0Bits.mono (by dsimp [B]; omega))
    oracle hspec delta hdelta f hf hcompatible model integerModel projectionCost gradientCost u hgrad
  change _ ∧ CompleteImplementationCertificate I oracle hspec (extendFinite (fun _=>0) f) E B T
    model integerModel projectionCost gradientCost ∧ _ ∧ _ ∧ _ at hh
  refine ⟨hh.1,hh.2.1,?_,hh.2.2.1,hh.2.2.2.1,?_⟩
  · exact countedRationalRegularity_program D G eta
  · simpa only [Nat.add_assoc] using
      Nat.add_le_add (regularity_charge_le D G eta b model) hh.2.2.2.2

end Paper254
#print axioms Paper254.rationalRegularity_work_heights
#print axioms Paper254.regularity_charge_le
#print axioms Paper254.raw_encoded_complete_all_path_implementation
