import FrontierState254
import ExplicitFrontier254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem aggregationPrediction_congr_prefix {d n : ℕ} {D : ℝ} {W : Domain d D}
    (p : ProbabilityWeights (Fin n)) (eta : ℝ) (f : ℕ → Loss d)
    (x y : ℕ → Fin n → W.carrier) (t : ℕ) (heq : ∀ s≤t, x s=y s) :
    aggregationPrediction p eta f x t=aggregationPrediction p eta f y t := by
  have hw := aggregationWeights_causal p eta (fun s j => f s (x s j).val)
    (fun s j => f s (y s j).val) t (fun s hs => by dsimp only; rw [heq s hs.le])
  simp only [aggregationPrediction,hw,heq t le_rfl]

theorem gradient_aggregation_predictions {d T K : ℕ} {D : ℝ} (W : Domain d D)
    (G eta : ℝ) (alpha : Fin (K+1) → ℝ) (w0 : W.carrier)
    (f : Fin T → Loss d) (t : Fin T) :
    predictions (aggregateOnline (uniformWeights K) eta w0
      (fun k => onlineProjectedGradient W G (alpha k) w0)) f t=
    aggregationPrediction (uniformWeights K) eta (extendFinite (fun _ => 0) f)
      (fun s k => projectedGradientTrajectory W G (alpha k) (extendFinite (fun _ => 0) f) w0 s) t.val := by
  rw [aggregateOnline_predictions]
  apply aggregationPrediction_congr_prefix
  intro s hs
  funext k
  have hsT : s<T := lt_of_le_of_lt hs t.isLt
  rw [expertTrajectory_predictions w0 (onlineProjectedGradient W G (alpha k) w0) f ⟨s,hsT⟩]
  exact projectedGradient_predictions W G (alpha k) w0 f ⟨s,hsT⟩

def frontierWithBase {d T : ℕ} {D : ℝ} (W : Domain d D) (G eta : ℝ)
    (w0 : W.carrier) (curved : OnlineLearner W T) : OnlineLearner W T :=
  aggregateOnline (uniformWeights 1) eta w0
    (fun j : Fin 2 => if j.val=0 then curved else scaledAdaptiveGradient W G eta w0)

/-- The cached state program refines the same nested learner used in the
full-frontier regret proof. Its additional oracle calls and arithmetic are
given by the explicit round counter, not assumed for the whole learner. -/
theorem frontier_runtime_prediction {d T : ℕ} {D : ℝ} (W : Domain d D)
    (lc gc pc ec : ℕ) (G eta : ℝ) (w0 : W.carrier) (curved : OnlineLearner W T)
    (f : Fin T → Loss d) (t : Fin T) :
    let ff := extendFinite (fun _ => 0) f
    let curve := expertTrajectory w0 curved ff
    (frontierStateRun W lc gc pc ec G eta
      (fun k : Fin (scaleCount T+1) => dyadicScale (2*D/G) k.val) w0 ff curve t.val).prediction (curve t.val)=
      predictions (frontierWithBase W G eta w0 curved) f t := by
  intro ff curve
  rw [frontierStateRun_prediction]
  unfold frontierWithBase
  rw [aggregateOnline_predictions]
  apply aggregationPrediction_congr_prefix
  intro s hs
  funext j
  have hsT : s<T := lt_of_le_of_lt hs t.isLt
  unfold frontierOuterPaths
  by_cases hj : j.val=0
  · simp only [hj,ite_true]
    rfl
  · simp only [hj,ite_false]
    rw [expertTrajectory_predictions w0 (scaledAdaptiveGradient W G eta w0) f ⟨s,hsT⟩]
    exact (gradient_aggregation_predictions W G eta
      (fun k : Fin (scaleCount T+1) => dyadicScale (2*D/G) k.val) w0 f ⟨s,hsT⟩).symm

theorem frontier_overhead_log_bound (d T lc gc pc ec : ℕ) (hT : 0<T) :
    (((scaleCount T+1)*(4*d+lc+gc+pc+ec+6)+4*d+2*lc+2*(ec+6) : ℕ) : ℝ)≤
      20*logFactor T*((d+lc+gc+pc+ec+2 : ℕ) : ℝ) := by
  have hN := scaleDepth_log_bound T hT
  have hL := logFactor_ge_one T hT
  have hm := mul_le_mul_of_nonneg_right hN
    (show (0 : ℝ)≤4*d+lc+gc+pc+ec+6 by positivity)
  have hd := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg d : (0 : ℝ)≤d)
  have hlc := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg lc : (0 : ℝ)≤lc)
  have hgc := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg gc : (0 : ℝ)≤gc)
  have hpc := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg pc : (0 : ℝ)≤pc)
  have hec := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg ec : (0 : ℝ)≤ec)
  push_cast at *
  nlinarith

theorem frontier_queries_log_bound (T : ℕ) (hT : 0<T) :
    (scaleCount T+3 : ℝ)≤4*logFactor T ∧
    (scaleCount T+2 : ℝ)≤3*logFactor T ∧
    (scaleCount T+1 : ℝ)≤2*logFactor T := by
  have hN := scaleDepth_log_bound T hT
  have hL := logFactor_ge_one T hT
  constructor
  · linarith
  exact ⟨by linarith,hN⟩

theorem frontier_storage_log_bound {d T : ℕ} {D : ℝ} {W : Domain d D}
    (S : FrontierState W (scaleCount T)) (hT : 0<T) :
    (S.storedScalars : ℝ)≤4*logFactor T*(d+1 : ℝ) := by
  rw [S.storedScalars_eq]
  push_cast
  have hN := scaleDepth_log_bound T hT
  have hL := logFactor_ge_one T hT
  have hm := mul_le_mul_of_nonneg_right hN (show (0 : ℝ)≤d+1 by positivity)
  have hd := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg d : (0 : ℝ)≤d)
  nlinarith

end Paper254
#print axioms Paper254.frontier_runtime_prediction
#print axioms Paper254.frontier_overhead_log_bound
