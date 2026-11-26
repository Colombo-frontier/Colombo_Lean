import SecondOrder.CurvaturePrefixResponse
import SecondOrder.CappedInformationEvent

open MeasureTheory InformationTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {S : Type} [Fintype S] {m T : ℕ} {R : ℝ}

def curvatureArrayInformation (m : ℕ) (R : ℝ) : ℝ := (Fintype.card (UpperPair (2*m)):ℝ)/R^2

theorem curvatureArrayInformation_nonneg (m : ℕ) (R : ℝ) : 0≤curvatureArrayInformation m R :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg R)

theorem curvatureArrayInformation_eq (m : ℕ) (R : ℝ) :
    curvatureArrayInformation m R=(((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2) := by
  unfold curvatureArrayInformation
  rw [upperPair_card_real]
  ring

def curvatureStageSelected
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ) (stage : ℕ)
    (n : ℕ) (h : FiniteHistory S (CurvatureCoefficients m T R) n) : Bool := decide (index n h=stage)

def curvatureStageTrue (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ)
    (n : ℕ) (h : FiniteHistory S (CurvatureCoefficients m T R) n) : PMF (CurvatureCoefficients m T R) :=
  curvaturePrefixCoefficientLaw (Θ (finiteHistoryInitial n h)) R hR (index n h+1)

/-- Fairly replace exactly the fresh array of the selected stage. -/
def curvatureStageReference (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ) (stage : ℕ)
    (n : ℕ) (h : FiniteHistory S (CurvatureCoefficients m T R) n) : PMF (CurvatureCoefficients m T R) :=
  curvaturePrefixCoefficientLaw (Θ (finiteHistoryInitial n h)) R hR
    (if index n h=stage then stage else index n h+1)

def curvatureStageDummy (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (n : ℕ) (h : FiniteHistory S (CurvatureCoefficients m T R) n) : PMF (CurvatureCoefficients m T R) :=
  curvaturePrefixCoefficientLaw (Θ (finiteHistoryInitial n h)) R hR 0

theorem curvatureStageTrue_ne_zero (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ) :
    ∀ n h a, curvatureStageTrue Θ R hR index n h a≠0 :=
  fun n h => curvaturePrefixCoefficientLaw_ne_zero _ R hR _

theorem curvatureStageReference_ne_zero (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ) (stage : ℕ) :
    ∀ n h a, curvatureStageReference Θ R hR index stage n h a≠0 :=
  fun n h => curvaturePrefixCoefficientLaw_ne_zero _ R hR _

theorem curvatureStageDummy_ne_zero (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R) :
    ∀ n h a, curvatureStageDummy Θ R hR n h a≠0 :=
  fun n h => curvaturePrefixCoefficientLaw_ne_zero _ R hR _

theorem curvatureStage_pmfKL (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ)
    {stage : ℕ} (hs : stage≤T) :
    ∀ n h, pmfKL (curvatureStageTrue Θ R hR index n h) (curvatureStageReference Θ R hR index stage n h)≤
      if curvatureStageSelected index stage n h=true then curvatureArrayInformation m R else 0 := by
  intro n h
  by_cases he : index n h=stage
  · simp only [curvatureStageSelected, he, decide_true, if_true, curvatureStageTrue, curvatureStageReference]
    rw [curvatureArrayInformation_eq]
    exact curvaturePrefixCoefficientLaw_pmfKL _ R hR hs
  · simp only [curvatureStageSelected, he, decide_false, Bool.false_eq_true, if_false,
      curvatureStageTrue, curvatureStageReference, if_neg he, pmfKL_self, le_refl]

/-- Actual coefficient sampling in the capped adaptive curvature continuation
has the manuscript's total information budget. The stage index may be any
history-dependent rule; stage-entry independence is a separate obligation. -/
theorem curvatureCappedExperiment_pmfKL (p : PMF S)
    (Θ : S → Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (CurvatureCoefficients m T R) n → ℕ)
    {stage : ℕ} (hs : stage≤T) (cap n : ℕ) (hp : ∀ s, p s≠0) :
    pmfKL
      (finiteAdaptiveLaw p (cappedTransition (curvatureStageSelected index stage) cap
        (curvatureStageTrue Θ R hR index) (curvatureStageDummy Θ R hR)) n)
      (finiteAdaptiveLaw p (cappedTransition (curvatureStageSelected index stage) cap
        (curvatureStageReference Θ R hR index stage) (curvatureStageDummy Θ R hR)) n)≤
      curvatureArrayInformation m R*cap :=
  cappedAdaptiveLaw_pmfKL_le p _ cap _ _ _ hp
    (curvatureStageTrue_ne_zero Θ R hR index) (curvatureStageReference_ne_zero Θ R hR index stage)
    (curvatureStageDummy_ne_zero Θ R hR) (curvatureArrayInformation_nonneg m R)
    (curvatureStage_pmfKL Θ R hR index hs) n

end
end SecondOrder
