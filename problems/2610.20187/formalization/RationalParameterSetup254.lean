import RationalInitializationCost254
import RationalExplicitOnline254

open scoped BigOperators
namespace Paper254

/-- Numerical parameters are cached for all scales once. The shared powers
and clipping margin are evaluated once, outside the scale traversal. -/
def countedParameterSetup (d K s v : ℕ) (hi : ℚ) :
    (Vector RationalHistoryParameters (K+1)×ℕ)×ℕ :=
  let r := explicitSparseHistoryPrecision d s v
  let n := 4*v+r+6
  let smoothPower := countedRatPow 2 n
  let guardPower := countedRatPow 2 (r+2)
  let smoothing := smoothPower.1⁻¹
  let guard := guardPower.1⁻¹
  let upper := hi-guard
  let cap := hi/4
  let rows := Vector.ofFn (fun k : Fin (K+1) =>
    let scalePower := countedRatPow 2 k.val
    let lo := min (hi/(scalePower.1*scalePower.1)) cap
    (({ dimensionLog := v, spectralLog := n+v+2, accuracy := n, storagePrecision := n,
        projectionPrecision := r, smoothing := smoothing, lowerThreshold := lo+guard,
        upperThreshold := upper } : RationalHistoryParameters),scalePower.2+4))
  ((rows.map Prod.fst,smoothPower.2+guardPower.2+4+(rows.toList.map Prod.snd).sum),
    20+4*(K+1))

theorem countedParameterSetup_value (d K s v : ℕ) (hi : ℚ) (k : Fin (K+1)) :
    ((countedParameterSetup d K s v hi).1.1.get k)=
      uniformHistoryParameters v v (explicitSparseHistoryPrecision d s v)
        (explicitSparseHistoryPrecision d s v) (rationalCappedVariance hi k.val) hi := by
  have hn : 3*v+v+explicitSparseHistoryPrecision d s v+6=4*v+explicitSparseHistoryPrecision d s v+6 := by omega
  simp [countedParameterSetup,Vector.get,countedRatPow_spec,uniformHistoryParameters,
    rationalCappedVariance,pow_two,hn]

def parameterSetupRationalBound (d K s v : ℕ) : ℕ :=
  4*v+2*explicitSparseHistoryPrecision d s v+12+(K+1)*(K+4)

theorem countedParameterSetup_rational (d K s v : ℕ) (hi : ℚ) :
    (countedParameterSetup d K s v hi).1.2≤parameterSetupRationalBound d K s v := by
  have hs : (∑ k : Fin (K+1),(k.val+4))≤(K+1)*(K+4) := by
    calc _≤∑ _k : Fin (K+1),(K+4) := Finset.sum_le_sum (by intro (k : Fin (K+1)) _; have := k.isLt; omega)
         _=_ := by simp
  simp only [countedParameterSetup,countedRatPow_spec,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply]
  dsimp only [parameterSetupRationalBound]
  omega

namespace ExplicitRationalSparseInput
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (I : ExplicitRationalSparseInput d T D G eta W)

theorem parameterSetup_program (k : Fin (scaleCount T+1)) :
    (countedParameterSetup d (scaleCount T) I.s I.v I.hi).1.1.get k=I.construction.cfg k :=
  countedParameterSetup_value d (scaleCount T) I.s I.v I.hi k

end ExplicitRationalSparseInput
end Paper254
#print axioms Paper254.countedParameterSetup_value
#print axioms Paper254.countedParameterSetup_rational
#print axioms Paper254.ExplicitRationalSparseInput.parameterSetup_program
