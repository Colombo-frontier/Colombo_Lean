import RationalMaterializedRun254
import RationalTotalCost254

noncomputable section
open scoped BigOperators
namespace Paper254
namespace RationalSparseConstruction
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T (scaleCount T) D G eta W)

def materializedRoundCharge (roundCost projectionCost gradientCost t : ℕ) : ℕ :=
  let S := ((C.materializedRun roundCost projectionCost gradientCost t).compactView
    ((standardRationalSchedule T (scaleCount T)).live t) (rationalHistoryInitial C.initial_mean C.hi)).ambient
      (rationalHistoryInitial C.initial_mean C.hi)
  (countedRationalRound C.master_precision roundCost projectionCost gradientCost C.oracle C.allCfg
    ((standardRationalSchedule T (scaleCount T)).live t)
    ((standardRationalSchedule T (scaleCount T)).live (t+1))
    ((standardRationalSchedule T (scaleCount T)).prior t)
    ((standardRationalSchedule T (scaleCount T)).share t) C.lam S (C.query t)).2

/-- Rational arithmetic and oracle charges of the actual list transition,
including the single queried gradient, both cached normalizers, and every
history update. Key lookups and list bookkeeping are separate integer work. -/
theorem materialized_total_cost (hT : 0 < T) (roundCost projectionCost gradientCost B : ℕ)
    (hcfg : ∀ e, historyStepCostBound d roundCost projectionCost (C.allCfg e)≤B) :
    (∑ t∈Finset.range T,(C.materializedRoundCharge roundCost projectionCost gradientCost t : ℝ))≤
      40*T*logFactor T^2*(B+5*d+6*C.master_precision+2*roundCost+65 : ℝ)+
        T*(2*C.master_precision+4+gradientCost : ℝ) :=
  countedStandardRounds_total_cost C.dimension_pos hT C.master_precision roundCost projectionCost gradientCost
    C.oracle C.allCfg C.lam (fun t =>
      ((C.materializedRun roundCost projectionCost gradientCost t).compactView
        ((standardRationalSchedule T (scaleCount T)).live t) (rationalHistoryInitial C.initial_mean C.hi)).ambient
          (rationalHistoryInitial C.initial_mean C.hi)) C.query B hcfg

theorem materialized_storage_log (hT : 0 < T) (roundCost projectionCost gradientCost t : ℕ) :
    ((C.materializedRun roundCost projectionCost gradientCost t).histories.length*(d*d+d)+
      (C.materializedRun roundCost projectionCost gradientCost t).weights.length : ℝ)≤
        40*logFactor T^2*((d : ℝ)^2+d+1) := by
  have hh : ((C.materializedRun roundCost projectionCost gradientCost t).histories.length*(d*d+d)+
      (C.materializedRun roundCost projectionCost gradientCost t).weights.length : ℝ)≤
        standardLiveCap T (scaleCount T)*((d : ℝ)^2+d+1) := by
    have hm := C.materializedRun_storage roundCost projectionCost gradientCost t
    push_cast at hm ⊢
    rw [pow_two]
    exact_mod_cast hm
  exact hh.trans (mul_le_mul_of_nonneg_right (standardLiveCap_log_bound T hT) (by positivity))

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.materialized_total_cost
#print axioms Paper254.RationalSparseConstruction.materialized_storage_log
