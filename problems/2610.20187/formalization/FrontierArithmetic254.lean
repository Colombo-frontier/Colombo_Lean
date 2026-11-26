import ExactRealArithmetic254
import ScaledAdaptive254
import CompactSparse254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem space_weighted_sum_apply {d n : ℕ} (p : Fin n → ℝ) (x : Fin n → Space d)
    (j : Fin d) : (∑ k,p k • x k) j=∑ k,p k*x k j := by
  have hh (s : Finset (Fin n)) : (∑ k∈s,p k • x k) j=∑ k∈s,p k*x k j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih => simp [hk,ih]
  exact hh Finset.univ

/-- Cached real exponential aggregation, in the paper's real-arithmetic
model. Exponential evaluation is charged separately from field operations. -/
def countedRealExponential {n : ℕ} (expCost : ℕ) (p : ProbabilityWeights (Fin n))
    (eta : ℝ) (loss : Fin n → ℝ) : (Fin n → ℝ)×ℕ :=
  let raw := countedRealVector (fun j => (p.weight j*Real.exp (-eta*loss j),expCost+3))
  let normal := countedRealDot (List.ofFn (fun j => (1,raw.1 j)))
  let out := countedRealVector (fun j => (raw.1 j/normal.1,1))
  (out.1,raw.2+normal.2+out.2)

theorem countedRealExponential_value {n : ℕ} (expCost : ℕ) (p : ProbabilityWeights (Fin n))
    (eta : ℝ) (loss : Fin n → ℝ) :
    (countedRealExponential expCost p eta loss).1=(p.exponential eta loss).weight := by
  ext j
  simp [countedRealExponential,countedRealVector_value,countedRealDot_spec,
    List.map_ofFn,List.sum_ofFn,ProbabilityWeights.exponential,exponentialUpdate,exponentialNormalizer]

theorem countedRealExponential_cost {n : ℕ} (expCost : ℕ) (p : ProbabilityWeights (Fin n))
    (eta : ℝ) (loss : Fin n → ℝ) :
    (countedRealExponential expCost p eta loss).2=n*(expCost+6) := by
  unfold countedRealExponential
  dsimp only
  rw [countedRealVector_cost _ (by intro j; rfl),countedRealVector_cost _ (by intro j; rfl)]
  simp only [countedRealDot_spec,List.length_ofFn]
  change n*(expCost+3)+2*n+n*1=n*(expCost+6)
  ring

def countedExponentialWeights {n : ℕ} (expCost : ℕ) (p : ProbabilityWeights (Fin n))
    (eta : ℝ) (loss : Fin n → ℝ) : ProbabilityWeights (Fin n)×ℕ :=
  let out := countedRealExponential expCost p eta loss
  (⟨out.1,(by rw [countedRealExponential_value]; exact (p.exponential eta loss).nonneg),
    (by rw [countedRealExponential_value]; exact (p.exponential eta loss).total)⟩,out.2)

theorem countedExponentialWeights_value {n : ℕ} (expCost : ℕ) (p : ProbabilityWeights (Fin n))
    (eta : ℝ) (loss : Fin n → ℝ) :
    (countedExponentialWeights expCost p eta loss).1=p.exponential eta loss := by
  apply ProbabilityWeights.ext
  intro j
  exact congrFun (countedRealExponential_value expCost p eta loss) j

def countedProjectedGradient {d : ℕ} {D : ℝ} (W : Domain d D)
    (gradientCost projectionCost : ℕ) (G alpha : ℝ) (f : Loss d) (z : W.carrier) : W.carrier×ℕ :=
  let g := selectedGradient W G f z
  let shifted := countedRealVector (fun j => (z.val j-alpha*g j,2))
  (metricProject W (ContinuousLinearEquiv.refl ℝ (Space d)) (WithLp.toLp 2 shifted.1),
    shifted.2+gradientCost+projectionCost)

theorem countedProjectedGradient_value {d : ℕ} {D : ℝ} (W : Domain d D)
    (gradientCost projectionCost : ℕ) (G alpha : ℝ) (f : Loss d) (z : W.carrier) :
    (countedProjectedGradient W gradientCost projectionCost G alpha f z).1=
      projectedGradientStep W G alpha f z := by
  unfold countedProjectedGradient projectedGradientStep
  dsimp only
  rw [countedRealVector_value]
  congr 1

theorem countedProjectedGradient_cost {d : ℕ} {D : ℝ} (W : Domain d D)
    (gradientCost projectionCost : ℕ) (G alpha : ℝ) (f : Loss d) (z : W.carrier) :
    (countedProjectedGradient W gradientCost projectionCost G alpha f z).2=
      2*d+gradientCost+projectionCost := by
  unfold countedProjectedGradient
  dsimp only
  rw [countedRealVector_cost _ (by intro j; rfl)]
  ring

def countedWeightedPoint {d n : ℕ} {D : ℝ} {W : Domain d D}
    (p : ProbabilityWeights (Fin n)) (x : Fin n → W.carrier) : W.carrier×ℕ := by
  let out := countedRealVector (fun j => countedRealDot (List.ofFn (fun k => (p.weight k,(x k).val j))))
  have he : WithLp.toLp 2 out.1=(weightedPrediction p.weight x p.nonneg p.total).val := by
    ext j
    simp [out,countedRealVector_value,countedRealDot_spec,List.map_ofFn,List.sum_ofFn,
      weightedPrediction,space_weighted_sum_apply]
  exact (⟨WithLp.toLp 2 out.1,by rw [he]; exact (weightedPrediction p.weight x p.nonneg p.total).property⟩,out.2)

theorem countedWeightedPoint_value {d n : ℕ} {D : ℝ} {W : Domain d D}
    (p : ProbabilityWeights (Fin n)) (x : Fin n → W.carrier) :
    (countedWeightedPoint p x).1=weightedPrediction p.weight x p.nonneg p.total := by
  apply Subtype.ext
  ext j
  simp [countedWeightedPoint,countedRealVector_value,countedRealDot_spec,
    List.map_ofFn,List.sum_ofFn,weightedPrediction,space_weighted_sum_apply]

theorem countedWeightedPoint_cost {d n : ℕ} {D : ℝ} {W : Domain d D}
    (p : ProbabilityWeights (Fin n)) (x : Fin n → W.carrier) :
    (countedWeightedPoint p x).2=2*d*n := by
  unfold countedWeightedPoint
  rw [countedRealVector_cost _ (c := 2*n) (by intro j; simp [countedRealDot_spec])]
  ring

end Paper254
#print axioms Paper254.countedProjectedGradient_value
#print axioms Paper254.countedRealExponential_value
#print axioms Paper254.countedWeightedPoint_value
