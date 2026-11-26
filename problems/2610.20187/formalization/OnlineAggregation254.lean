import FiniteAggregation254
import FiniteInterface254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem aggregationWeights_causal {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (η : ℝ) (loss loss' : ℕ → ι → ℝ) (t : ℕ)
    (h : ∀ s < t, loss s = loss' s) :
    aggregationWeights p η loss t = aggregationWeights p η loss' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [aggregationWeights]
    rw [h t (Nat.lt_succ_self t), ih (fun s hs => h s (Nat.lt.step hs))]

def expertTrajectory {d T : ℕ} {D : ℝ} {W : Domain d D}
    (w0 : W.carrier) (A : OnlineLearner W T) (f : ℕ → Loss d) (n : ℕ) : W.carrier :=
  if hn : n < T then A ⟨n,hn⟩ (fun s => f s.val) else w0

theorem expertTrajectory_causal {d T : ℕ} {D : ℝ} {W : Domain d D}
    (w0 : W.carrier) (A : OnlineLearner W T) (f g : ℕ → Loss d) (n : ℕ)
    (h : ∀ s < n, f s = g s) : expertTrajectory w0 A f n = expertTrajectory w0 A g n := by
  unfold expertTrajectory
  split_ifs with hn
  · congr 1
    funext s
    exact h s.val s.isLt
  · rfl

def aggregateOnline {d T : ℕ} {D : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (η : ℝ)
    (w0 : W.carrier) (A : ι → OnlineLearner W T) : OnlineLearner W T :=
  fun t history =>
    let f : ℕ → Loss d := extendFinite (fun _ => 0) history
    aggregationPrediction p η f (fun n j => expertTrajectory w0 (A j) f n) t.val

theorem aggregateOnline_predictions {d T : ℕ} {D : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (η : ℝ)
    (w0 : W.carrier) (A : ι → OnlineLearner W T) (f : Fin T → Loss d) (t : Fin T) :
    predictions (aggregateOnline p η w0 A) f t =
      aggregationPrediction p η (extendFinite (fun _ => 0) f)
        (fun n j => expertTrajectory w0 (A j) (extendFinite (fun _ => 0) f) n) t.val := by
  let short := extendFinite (fun _ => 0) (past f t)
  let full := extendFinite (fun _ => 0) f
  have hh : ∀ s < t.val, short s = full s := by
    intro s hs
    have hsT := Nat.lt_trans hs t.isLt
    simp [short,full,extendFinite,hs,hsT,past]
  have hx : ∀ n ≤ t.val, (fun j => expertTrajectory w0 (A j) short n) =
      (fun j => expertTrajectory w0 (A j) full n) := by
    intro n hn
    funext j
    exact expertTrajectory_causal w0 (A j) short full n (fun s hs => hh s (lt_of_lt_of_le hs hn))
  have hw := aggregationWeights_causal p η
    (fun n j => short n (expertTrajectory w0 (A j) short n).val)
    (fun n j => full n (expertTrajectory w0 (A j) full n).val) t.val (by
      intro n hn
      funext j
      dsimp only
      rw [hh n hn, congrFun (hx n hn.le) j])
  change aggregationPrediction p η short (fun n j => expertTrajectory w0 (A j) short n) t.val =
    aggregationPrediction p η full (fun n j => expertTrajectory w0 (A j) full n) t.val
  apply Subtype.ext
  simp only [aggregationPrediction, weightedPrediction, hw]
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun (hx t.val (le_refl _)) j]

theorem expertTrajectory_predictions {d T : ℕ} {D : ℝ} {W : Domain d D}
    (w0 : W.carrier) (A : OnlineLearner W T) (f : Fin T → Loss d) (t : Fin T) :
    expertTrajectory w0 A (extendFinite (fun _ => 0) f) t.val = predictions A f t := by
  simp only [expertTrajectory, dif_pos t.isLt, predictions]
  congr 1
  funext s
  simp [extendFinite, Nat.lt_trans s.isLt t.isLt, past]

theorem aggregateOnline_regret {d T : ℕ} {D G η : ℝ} {W : Domain d D}
    {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (hη : 0 < η)
    (w0 : W.carrier) (A : ι → OnlineLearner W T)
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) (j : ι) (hj : 0 < p.weight j) :
    regret (aggregateOnline p η w0 A) f u ≤ regret (A j) f u-Real.log (p.weight j)/η := by
  let ff := extendFinite (fun _ => 0) f
  let xx := fun n k => expertTrajectory w0 (A k) ff n
  have hh := aggregation_regret_bound p hη ff xx T
    (by intro t ht; simpa [ff,extendFinite,ht] using (hf ⟨t,ht⟩).1) j hj
  have he : cumulative (fun t => ff t (aggregationPrediction p η ff xx t).val-ff t (xx t j).val) T =
      regret (aggregateOnline p η w0 A) f u-regret (A j) f u := by
    unfold cumulative regret
    rw [← Fin.sum_univ_eq_sum_range, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [aggregateOnline_predictions]
    simp only [ff, xx, extendFinite_at, expertTrajectory_predictions]
    ring
  rw [he] at hh
  rw [neg_div] at hh
  linarith

end Paper254
#print axioms Paper254.aggregateOnline_regret
