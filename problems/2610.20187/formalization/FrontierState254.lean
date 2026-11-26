import FrontierArithmetic254

noncomputable section
open scoped BigOperators
namespace Paper254

structure FrontierState {d : ℕ} {D : ℝ} (W : Domain d D) (K : ℕ) where
  points : Vector W.carrier (K+1)
  inner : ProbabilityWeights (Fin (K+1))
  outer : ProbabilityWeights (Fin 2)

namespace FrontierState
variable {d K : ℕ} {D : ℝ} {W : Domain d D}

def initial (w0 : W.carrier) : FrontierState W K :=
  ⟨Vector.replicate (K+1) w0,uniformWeights K,uniformWeights 1⟩

def innerPoint (S : FrontierState W K) : W.carrier :=
  (countedWeightedPoint S.inner S.points.get).1

def outerPoints (S : FrontierState W K) (curved : W.carrier) : Fin 2 → W.carrier :=
  fun j => if j.val=0 then curved else S.innerPoint

def prediction (S : FrontierState W K) (curved : W.carrier) : W.carrier :=
  (countedWeightedPoint S.outer (S.outerPoints curved)).1

/-- Materialized projected-gradient states and cached inner and outer
normalizers. The curved engine supplies its current proper prediction. -/
def round (S : FrontierState W K) (lossCost gradientCost projectionCost expCost : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier) :
    (W.carrier×FrontierState W K)×ℕ :=
  let innerPrediction := countedWeightedPoint S.inner S.points.get
  let outerPoints : Fin 2 → W.carrier := fun j => if j.val=0 then curved else innerPrediction.1
  let outerPrediction := countedWeightedPoint S.outer outerPoints
  let losses := countedRealVector (fun j => (f (S.points.get j).val,lossCost))
  let updates := Vector.ofFn (fun j => countedProjectedGradient W gradientCost projectionCost G (alpha j) f (S.points.get j))
  let innerNext := countedExponentialWeights expCost S.inner eta losses.1
  let outerLosses := countedRealVector (fun j => (f (outerPoints j).val,lossCost))
  let outerNext := countedExponentialWeights expCost S.outer eta outerLosses.1
  ((outerPrediction.1,⟨updates.map Prod.fst,innerNext.1,outerNext.1⟩),
    innerPrediction.2+outerPrediction.2+losses.2+(updates.toList.map Prod.snd).sum+
      innerNext.2+outerLosses.2+outerNext.2)

theorem round_prediction (S : FrontierState W K) (lc gc pc ec : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier) :
    (S.round lc gc pc ec G eta alpha f curved).1.1=S.prediction curved := rfl

theorem round_points (S : FrontierState W K) (lc gc pc ec : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier)
    (j : Fin (K+1)) :
    ((S.round lc gc pc ec G eta alpha f curved).1.2.points.get j)=
      projectedGradientStep W G (alpha j) f (S.points.get j) := by
  simp [round,Vector.get,countedProjectedGradient_value]

theorem round_inner (S : FrontierState W K) (lc gc pc ec : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier) :
    (S.round lc gc pc ec G eta alpha f curved).1.2.inner=
      S.inner.exponential eta (fun j => f (S.points.get j).val) := by
  simp [round,countedExponentialWeights_value,countedRealVector_value]

theorem round_outer (S : FrontierState W K) (lc gc pc ec : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier) :
    (S.round lc gc pc ec G eta alpha f curved).1.2.outer=
      S.outer.exponential eta (fun j => f (S.outerPoints curved j).val) := by
  simp only [round,countedExponentialWeights_value,countedRealVector_value]
  rfl

theorem round_cost (S : FrontierState W K) (lc gc pc ec : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier) :
    (S.round lc gc pc ec G eta alpha f curved).2=
      (K+1)*(4*d+lc+gc+pc+ec+6)+4*d+2*lc+2*(ec+6) := by
  simp only [round,countedWeightedPoint_cost,countedExponentialWeights,
    countedRealExponential_cost,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  rw [countedRealVector_cost _ (by intro j; rfl),countedRealVector_cost _ (by intro j; rfl)]
  simp only [Function.comp_apply,countedProjectedGradient_cost,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

/-- Raising one primitive's unit price by one measures its actual call
count in the materialized traversal. These counts include both masters. -/
theorem round_call_counts (S : FrontierState W K) (lc gc pc ec : ℕ)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (f : Loss d) (curved : W.carrier) :
    (S.round (lc+1) gc pc ec G eta alpha f curved).2=
      (S.round lc gc pc ec G eta alpha f curved).2+(K+3) ∧
    (S.round lc (gc+1) pc ec G eta alpha f curved).2=
      (S.round lc gc pc ec G eta alpha f curved).2+(K+1) ∧
    (S.round lc gc (pc+1) ec G eta alpha f curved).2=
      (S.round lc gc pc ec G eta alpha f curved).2+(K+1) := by
  simp only [round_cost]
  constructor
  · ring
  constructor <;> ring

def storedScalars (_S : FrontierState W K) : ℕ := (K+1)*d+(K+1)+2

theorem storedScalars_eq (S : FrontierState W K) : S.storedScalars=(K+1)*(d+1)+2 := by
  unfold storedScalars
  ring

end FrontierState

def frontierStateRun {d K : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (alpha : Fin (K+1) → ℝ)
    (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier) : ℕ → FrontierState W K
  | 0 => FrontierState.initial w0
  | t+1 => ((frontierStateRun W lc gc pc ec G eta alpha w0 f curved t).round
      lc gc pc ec G eta alpha (f t) (curved t)).1.2

theorem frontierStateRun_points {d K : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (alpha : Fin (K+1) → ℝ)
    (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier)
    (t : ℕ) (j : Fin (K+1)) :
    (frontierStateRun W lc gc pc ec G eta alpha w0 f curved t).points.get j=
      projectedGradientTrajectory W G (alpha j) f w0 t := by
  induction t with
  | zero => simp [frontierStateRun,FrontierState.initial,projectedGradientTrajectory,Vector.get]
  | succ t ih => simp only [frontierStateRun,FrontierState.round_points,projectedGradientTrajectory,ih]

theorem frontierStateRun_inner {d K : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (alpha : Fin (K+1) → ℝ)
    (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier) (t : ℕ) :
    (frontierStateRun W lc gc pc ec G eta alpha w0 f curved t).inner=
      aggregationWeights (uniformWeights K) eta
        (fun s j => f s (projectedGradientTrajectory W G (alpha j) f w0 s).val) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [frontierStateRun,FrontierState.round_inner,aggregationWeights,
      frontierStateRun_points,ih]

theorem frontierStateRun_innerPoint {d K : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (alpha : Fin (K+1) → ℝ)
    (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier) (t : ℕ) :
    (frontierStateRun W lc gc pc ec G eta alpha w0 f curved t).innerPoint=
      aggregationPrediction (uniformWeights K) eta f
        (fun s j => projectedGradientTrajectory W G (alpha j) f w0 s) t := by
  simp only [FrontierState.innerPoint,countedWeightedPoint_value,frontierStateRun_inner,
    aggregationPrediction]
  congr 1
  funext j
  exact frontierStateRun_points W lc gc pc ec G eta alpha w0 f curved t j

def frontierOuterPaths {d K : ℕ} {D : ℝ} (W : Domain d D) (G eta : ℝ)
    (alpha : Fin (K+1) → ℝ) (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier)
    (t : ℕ) (j : Fin 2) : W.carrier :=
  if j.val=0 then curved t else aggregationPrediction (uniformWeights K) eta f
    (fun s k => projectedGradientTrajectory W G (alpha k) f w0 s) t

theorem frontierStateRun_outer {d K : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (alpha : Fin (K+1) → ℝ)
    (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier) (t : ℕ) :
    (frontierStateRun W lc gc pc ec G eta alpha w0 f curved t).outer=
      aggregationWeights (uniformWeights 1) eta
        (fun s j => f s (frontierOuterPaths W G eta alpha w0 f curved s j).val) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [frontierStateRun,FrontierState.round_outer,aggregationWeights,
      FrontierState.outerPoints,frontierStateRun_innerPoint,frontierOuterPaths,ih]

theorem frontierStateRun_prediction {d K : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (alpha : Fin (K+1) → ℝ)
    (w0 : W.carrier) (f : ℕ → Loss d) (curved : ℕ → W.carrier) (t : ℕ) :
    (frontierStateRun W lc gc pc ec G eta alpha w0 f curved t).prediction (curved t)=
      aggregationPrediction (uniformWeights 1) eta f (frontierOuterPaths W G eta alpha w0 f curved) t := by
  simp only [FrontierState.prediction,countedWeightedPoint_value,frontierStateRun_outer,
    aggregationPrediction]
  congr 1
  funext j
  simp only [FrontierState.outerPoints,frontierOuterPaths,frontierStateRun_innerPoint]

theorem frontierStateRun_total_overhead {d T : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (w0 : W.carrier) (f : ℕ → Loss d)
    (curved : ℕ → W.carrier) :
    (∑ t : Fin T,((frontierStateRun W lc gc pc ec G eta
      (fun k : Fin (scaleCount T+1) => dyadicScale (2*D/G) k.val) w0 f curved t.val).round
      lc gc pc ec G eta (fun k => dyadicScale (2*D/G) k.val) (f t.val) (curved t.val)).2)=
      T*((scaleCount T+1)*(4*d+lc+gc+pc+ec+6)+4*d+2*lc+2*(ec+6)) := by
  simp only [FrontierState.round_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

end Paper254
#print axioms Paper254.frontierStateRun_innerPoint
#print axioms Paper254.FrontierState.round_cost
#print axioms Paper254.frontierStateRun_prediction
#print axioms Paper254.frontierStateRun_total_overhead
