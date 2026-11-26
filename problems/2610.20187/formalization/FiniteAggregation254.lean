import MasterWeights254
import Energy254

noncomputable section
open scoped BigOperators
namespace Paper254

def uniformWeights (N : ℕ) : ProbabilityWeights (Fin (N+1)) where
  weight _ := 1/(N+1 : ℝ)
  nonneg _ := by positivity
  total := by simp [ne_of_gt (show (0 : ℝ) < N+1 by positivity)]

def aggregationWeights {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (η : ℝ) (loss : ℕ → ι → ℝ) : ℕ → ProbabilityWeights ι
  | 0 => p
  | t+1 => (aggregationWeights p η loss t).exponential η (loss t)

theorem aggregationWeights_positive {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (η : ℝ) (loss : ℕ → ι → ℝ) (j : ι) (hj : 0 < p.weight j) (t : ℕ) :
    0 < (aggregationWeights p η loss t).weight j := by
  induction t with
  | zero => exact hj
  | succ t ih =>
    exact div_pos (mul_pos ih (Real.exp_pos _))
      (exponentialNormalizer_pos η _ _ (aggregationWeights p η loss t).nonneg j ih)

def aggregationPrediction {d : ℕ} {D : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (η : ℝ)
    (f : ℕ → Loss d) (x : ℕ → ι → W.carrier) (t : ℕ) : W.carrier :=
  let q := aggregationWeights p η (fun s j => f s (x s j).val) t
  weightedPrediction q.weight (x t) q.nonneg q.total

theorem aggregation_log_telescope {d : ℕ} {D η : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (f : ℕ → Loss d) (x : ℕ → ι → W.carrier) (N : ℕ)
    (hf : ∀ t < N, ExpConcaveOn η W.carrier (f t)) (j : ι) (hj : 0 < p.weight j) :
    η*cumulative (fun t => f t (aggregationPrediction p η f x t).val-f t (x t j).val) N ≤
      Real.log ((aggregationWeights p η (fun t k => f t (x t k).val) N).weight j)-Real.log (p.weight j) := by
  induction N with
  | zero => simp [cumulative,aggregationWeights]
  | succ N ih =>
    have hp := ih (fun t ht => hf t (Nat.lt.step ht))
    have hs := exponential_update_one_step
      (aggregationWeights p η (fun t k => f t (x t k).val) N).weight (x N)
      (aggregationWeights p η (fun t k => f t (x t k).val) N).nonneg
      (aggregationWeights p η (fun t k => f t (x t k).val) N).total
      (hf N (Nat.lt_succ_self N)) j (aggregationWeights_positive p η _ j hj N)
    rw [cumulative_succ]
    change η*(f N (aggregationPrediction p η f x N).val-f N (x N j).val) ≤
      Real.log ((aggregationWeights p η (fun t k => f t (x t k).val) (N+1)).weight j)-
      Real.log ((aggregationWeights p η (fun t k => f t (x t k).val) N).weight j) at hs
    nlinarith

theorem aggregation_regret_bound {d : ℕ} {D η : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (hη : 0 < η)
    (f : ℕ → Loss d) (x : ℕ → ι → W.carrier) (N : ℕ)
    (hf : ∀ t < N, ExpConcaveOn η W.carrier (f t)) (j : ι) (hj : 0 < p.weight j) :
    cumulative (fun t => f t (aggregationPrediction p η f x t).val-f t (x t j).val) N ≤
      -Real.log (p.weight j)/η := by
  have hh := aggregation_log_telescope p f x N hf j hj
  have hp := aggregationWeights_positive p η (fun t k => f t (x t k).val) j hj N
  have hlog := Real.log_le_log hp
    ((aggregationWeights p η (fun t k => f t (x t k).val) N).weight_le_one j)
  rw [Real.log_one] at hlog
  apply (le_div_iff₀ hη).mpr
  nlinarith

end Paper254
#print axioms Paper254.aggregation_regret_bound
