import SecondOrder.FirstOrderPrefixResponse
import SecondOrder.CappedInformationEvent

open MeasureTheory InformationTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {S : Type} [Fintype S] {d T : ℕ} {R : ℝ}

def firstOrderArrayInformation (d : ℕ) (R : ℝ) : ℝ := (Fintype.card (Fin d):ℝ)/R^2

theorem firstOrderArrayInformation_nonneg (d : ℕ) (R : ℝ) : 0≤firstOrderArrayInformation d R :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg R)

theorem firstOrderArrayInformation_eq (d : ℕ) (R : ℝ) :
    firstOrderArrayInformation d R=(d:ℝ)/R^2 := by
  unfold firstOrderArrayInformation
  rw [Fintype.card_fin]

def firstOrderStageSelected
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ) (stage : ℕ)
    (n : ℕ) (h : FiniteHistory S (FirstOrderCoefficients d T R) n) : Bool := decide (index n h=stage)

def firstOrderStageTrue (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ)
    (n : ℕ) (h : FiniteHistory S (FirstOrderCoefficients d T R) n) : PMF (FirstOrderCoefficients d T R) :=
  firstOrderPrefixCoefficientLaw (Θ (finiteHistoryInitial n h)) R hR (index n h+1)

/-- Fairly replace exactly the fresh array of the selected stage. -/
def firstOrderStageReference (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ) (stage : ℕ)
    (n : ℕ) (h : FiniteHistory S (FirstOrderCoefficients d T R) n) : PMF (FirstOrderCoefficients d T R) :=
  firstOrderPrefixCoefficientLaw (Θ (finiteHistoryInitial n h)) R hR
    (if index n h=stage then stage else index n h+1)

def firstOrderStageDummy (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (n : ℕ) (h : FiniteHistory S (FirstOrderCoefficients d T R) n) : PMF (FirstOrderCoefficients d T R) :=
  firstOrderPrefixCoefficientLaw (Θ (finiteHistoryInitial n h)) R hR 0

theorem firstOrderStageTrue_ne_zero (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ) :
    ∀ n h a, firstOrderStageTrue Θ R hR index n h a≠0 :=
  fun n h => firstOrderPrefixCoefficientLaw_ne_zero _ R hR _

theorem firstOrderStageReference_ne_zero (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ) (stage : ℕ) :
    ∀ n h a, firstOrderStageReference Θ R hR index stage n h a≠0 :=
  fun n h => firstOrderPrefixCoefficientLaw_ne_zero _ R hR _

theorem firstOrderStageDummy_ne_zero (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R) :
    ∀ n h a, firstOrderStageDummy Θ R hR n h a≠0 :=
  fun n h => firstOrderPrefixCoefficientLaw_ne_zero _ R hR _

theorem firstOrderStage_pmfKL (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ)
    {stage : ℕ} (hs : stage≤T) :
    ∀ n h, pmfKL (firstOrderStageTrue Θ R hR index n h) (firstOrderStageReference Θ R hR index stage n h)≤
      if firstOrderStageSelected index stage n h=true then firstOrderArrayInformation d R else 0 := by
  intro n h
  by_cases he : index n h=stage
  · simp only [firstOrderStageSelected, he, decide_true, if_true, firstOrderStageTrue, firstOrderStageReference]
    rw [firstOrderArrayInformation_eq]
    exact firstOrderPrefixCoefficientLaw_pmfKL _ R hR hs
  · simp only [firstOrderStageSelected, he, decide_false, Bool.false_eq_true, if_false,
      firstOrderStageTrue, firstOrderStageReference, if_neg he, pmfKL_self, le_refl]

/-- Actual coefficient sampling in the capped adaptive firstOrder continuation
has the manuscript's total information budget. The stage index may be any
history-dependent rule; stage-entry independence is a separate obligation. -/
theorem firstOrderCappedExperiment_pmfKL (p : PMF S)
    (Θ : S → Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory S (FirstOrderCoefficients d T R) n → ℕ)
    {stage : ℕ} (hs : stage≤T) (cap n : ℕ) (hp : ∀ s, p s≠0) :
    pmfKL
      (finiteAdaptiveLaw p (cappedTransition (firstOrderStageSelected index stage) cap
        (firstOrderStageTrue Θ R hR index) (firstOrderStageDummy Θ R hR)) n)
      (finiteAdaptiveLaw p (cappedTransition (firstOrderStageSelected index stage) cap
        (firstOrderStageReference Θ R hR index stage) (firstOrderStageDummy Θ R hR)) n)≤
      firstOrderArrayInformation d R*cap :=
  cappedAdaptiveLaw_pmfKL_le p _ cap _ _ _ hp
    (firstOrderStageTrue_ne_zero Θ R hR index) (firstOrderStageReference_ne_zero Θ R hR index stage)
    (firstOrderStageDummy_ne_zero Θ R hR) (firstOrderArrayInformation_nonneg d R)
    (firstOrderStage_pmfKL Θ R hR index hs) n

end
end SecondOrder

