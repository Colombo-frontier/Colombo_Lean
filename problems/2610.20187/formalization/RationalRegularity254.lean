import RationalEncodedInput254
import HistoryIntermediateHeight254

namespace Paper254

/-- Derived regularity parameters use only exact rational operations. -/
def rationalDiameterSquare (D : ℚ) : ℚ := D*D

def rationalCurvature (D G eta : ℚ) : ℚ := min (eta/2) (1/(4*G*D))

def rationalLearningRate (D G eta : ℚ) : ℚ := rationalCurvature D G eta/2

theorem rationalDiameterSquare_cast (D : ℚ) :
    (rationalDiameterSquare D:ℝ)=(D:ℝ)^2 := by
  simp [rationalDiameterSquare,pow_two]

theorem rationalCurvature_cast (D G eta : ℚ) :
    (rationalCurvature D G eta:ℝ)=curvature (D:ℝ) (G:ℝ) (eta:ℝ) := by
  simp [rationalCurvature,curvature]

theorem rationalLearningRate_cast (D G eta : ℚ) :
    2*(rationalLearningRate D G eta:ℝ)=curvature (D:ℝ) (G:ℝ) (eta:ℝ) := by
  simp [rationalLearningRate,rationalCurvature_cast]
  ring

theorem rationalDiameterSquare_height (D : ℚ) (b : ℕ) (hD : RationalHeight D b) :
    RationalHeight (rationalDiameterSquare D) (2*b+1) := by
  simpa only [rationalDiameterSquare,two_mul] using hD.mul hD

theorem rationalCurvature_height (D G eta : ℚ) (b : ℕ)
    (hD : RationalHeight D b) (hG : RationalHeight G b) (heta : RationalHeight eta b) :
    RationalHeight (rationalCurvature D G eta) (2*b+4) := by
  have h4 : RationalHeight (4:ℚ) 2 := by
    simpa using RationalHeight.of_int 4 2 (by norm_num)
  have hleft : RationalHeight (eta/2) (2*b+4) := by
    have hh := heta.mul rational_half_height
    rw [mul_one_div] at hh
    exact hh.mono (by omega)
  have hright : RationalHeight (1/(4*G*D)) (2*b+4) := by
    have hh := ((h4.mul hG).mul hD).inv
    simpa only [one_div,show 2+b+1+b+1=2*b+4 by omega] using hh
  unfold rationalCurvature
  by_cases h : eta/2≤1/(4*G*D)
  · simpa only [min_eq_left h] using hleft
  · simpa only [min_eq_right (le_of_not_ge h)] using hright

theorem rationalLearningRate_height (D G eta : ℚ) (b : ℕ)
    (hD : RationalHeight D b) (hG : RationalHeight G b) (heta : RationalHeight eta b) :
    RationalHeight (rationalLearningRate D G eta) (2*b+6) := by
  have hh := (rationalCurvature_height D G eta b hD hG heta).mul rational_half_height
  simpa only [rationalLearningRate,mul_one_div,show 2*b+4+1+1=2*b+6 by omega] using hh

/-- Six rational arithmetic instructions and one rational comparison.
The counters count those primitive calls, not machine instructions. -/
def countedRationalRegularity (D G eta : ℚ) : (ℚ×ℚ)×(ℕ×ℕ) :=
  let H := D*D
  let left := eta/2
  let fourG := 4*G
  let denominator := fourG*D
  let right := 1/denominator
  let gamma := if left≤right then left else right
  let lam := gamma/2
  ((H,lam),(6,1))

theorem countedRationalRegularity_program (D G eta : ℚ) :
    (countedRationalRegularity D G eta).1=
      (rationalDiameterSquare D,rationalLearningRate D G eta) := by
  simp [countedRationalRegularity,rationalDiameterSquare,rationalLearningRate,rationalCurvature,min_def]

theorem countedRationalRegularity_cost (D G eta : ℚ) :
    (countedRationalRegularity D G eta).2=(6,1) := rfl

noncomputable section

/-- The explicit numerical input can be obtained directly from rational
diameter, gradient and exp-concavity parameters. The two derived-parameter
equalities are proved, rather than requested from an additional oracle. -/
def encodedRationalInputFromRegularity {d T : ℕ} (hd : 0<d)
    (D G eta : ℚ) (W : Domain d (D:ℝ))
    (hD : 0<(D:ℝ)) (hG : 0<(G:ℝ)) (heta : 0<(eta:ℝ))
    (b z : ℕ) (hDb : RationalHeight D b) (hGb : RationalHeight G b)
    (hetab : RationalHeight eta b)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier) :
    ExplicitRationalSparseInput d T (D:ℝ) (G:ℝ) (eta:ℝ) W :=
  encodedRationalSparseInput hd D G (rationalDiameterSquare D) (rationalLearningRate D G eta)
    (eta:ℝ) W hD hG heta (rationalDiameterSquare_cast D) (rationalLearningRate_cast D G eta)
    (2*b+6) z (hDb.mono (by omega)) (hGb.mono (by omega))
    ((rationalDiameterSquare_height D b hDb).mono (by omega))
    (rationalLearningRate_height D G eta b hDb hGb hetab) oracle hspec w0 hw0

end
end Paper254
#print axioms Paper254.rationalLearningRate_cast
#print axioms Paper254.rationalCurvature_height
#print axioms Paper254.rationalLearningRate_height
#print axioms Paper254.countedRationalRegularity_program
#eval decide ((Paper254.countedRationalRegularity 1 2 (1/2)).1=(1,1/16))
