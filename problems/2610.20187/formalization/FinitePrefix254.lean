import FiniteInterface254

noncomputable section
open scoped BigOperators
namespace Paper254

def prefixLearner {d m H : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W H) (hm : m ≤ H) : OnlineLearner W m :=
  fun t history => A ⟨t.val,lt_of_lt_of_le t.isLt hm⟩ history

def paddedLoss {d m H : ℕ} (f : Fin m → Loss d) : Fin H → Loss d :=
  fun t => if ht : t.val < m then f ⟨t.val,ht⟩ else fun _ => 0

def paddedComparator {d m H : ℕ} {D : ℝ} {W : Domain d D}
    (hm : 0 < m) (u : Fin m → W.carrier) : Fin H → W.carrier :=
  fun t => if ht : t.val < m then u ⟨t.val,ht⟩ else u ⟨m-1,by omega⟩

theorem finite_sum_zero_tail (m H : ℕ) (hm : m ≤ H) (f : ℕ → ℝ)
    (hz : ∀ i,m ≤ i → i < H → f i=0) :
    (∑ i : Fin H,f i.val) = ∑ i : Fin m,f i.val := by
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i hi hni
  exact hz i (by simpa using hni) (Finset.mem_range.mp hi)

theorem prefix_predictions {d m H : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W H) (hm : m ≤ H) (f : Fin m → Loss d) (t : Fin m) :
    predictions A (paddedLoss f) ⟨t.val,lt_of_lt_of_le t.isLt hm⟩ =
      predictions (prefixLearner A hm) f t := by
  unfold predictions prefixLearner
  congr 1
  funext j
  simp [past,paddedLoss,lt_trans j.isLt t.isLt]

theorem prefix_regret {d m H : ℕ} {D : ℝ} {W : Domain d D}
    (A : OnlineLearner W H) (hm : m ≤ H) (hm0 : 0 < m)
    (f : Fin m → Loss d) (u : Fin m → W.carrier) :
    regret A (paddedLoss f) (paddedComparator hm0 u)=regret (prefixLearner A hm) f u := by
  let r : ℕ → ℝ := fun n => if hn : n < m then
    f ⟨n,hn⟩ (predictions (prefixLearner A hm) f ⟨n,hn⟩).val-f ⟨n,hn⟩ (u ⟨n,hn⟩).val else 0
  have h1 : regret A (paddedLoss f) (paddedComparator hm0 u)=∑ t : Fin H,r t.val := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < m
    · have hp := prefix_predictions A hm f ⟨t.val,ht⟩
      simpa only [paddedLoss,paddedComparator,dif_pos ht,r] using
        congrArg (fun z : W.carrier => f ⟨t.val,ht⟩ z.val-f ⟨t.val,ht⟩ (u ⟨t.val,ht⟩).val) hp
    · simp [paddedLoss,ht,r]
  rw [h1,finite_sum_zero_tail m H hm r (by intro i hi _; simp [r,show ¬ i < m by omega])]
  apply Finset.sum_congr rfl
  intro t _
  simp [r,t.isLt]

theorem padded_pathLength {d m H : ℕ} {D : ℝ} {W : Domain d D}
    (hm : m ≤ H) (hm0 : 0 < m) (u : Fin m → W.carrier) :
    pathLength (paddedComparator (H := H) hm0 u)=pathLength u := by
  let p : ℕ → ℝ := fun n => if hn : n < m then
    if hp : 0 < n then ‖(u ⟨n,hn⟩).val-(u ⟨n-1,by omega⟩).val‖ else 0 else 0
  have he : pathLength (paddedComparator (H := H) hm0 u)=∑ t : Fin H,p t.val := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < m
    · by_cases hp : 0 < t.val
      · simp [pathLength,paddedComparator,p,ht,hp,show t.val-1 < m by omega]
      · simp [pathLength,p,hp]
    · have hp : 0 < t.val := by omega
      by_cases heq : t.val=m
      · have hprev : t.val-1 < m := by omega
        simp [pathLength,paddedComparator,p,ht,hp,hprev,heq,hm0]
      · have hprev : ¬ t.val-1 < m := by omega
        simp [pathLength,paddedComparator,p,ht,hp,hprev]
  rw [he,finite_sum_zero_tail m H hm p (by intro i hi _; simp [p,show ¬ i < m by omega])]
  apply Finset.sum_congr rfl
  intro t _
  simp [p,t.isLt]

theorem zero_loss_admissible {d : ℕ} {D G η : ℝ} (W : Domain d D) (hG : 0 ≤ G) :
    AdmissibleLoss W G η (fun _ => 0) := by
  constructor
  · unfold ExpConcaveOn
    simpa using concaveOn_const (c := (1:ℝ)) W.convex
  · intro w hw
    refine ⟨0,?_,by simpa using hG⟩
    simpa using (hasFDerivWithinAt_const (0:ℝ) w W.carrier).hasGradientWithinAt

theorem padded_admissible {d m H : ℕ} {D G η : ℝ} (W : Domain d D) (hG : 0 ≤ G)
    (f : Fin m → Loss d) (hf : ∀ t,AdmissibleLoss W G η (f t)) :
    ∀ t : Fin H,AdmissibleLoss W G η (paddedLoss f t) := by
  intro t
  unfold paddedLoss
  split_ifs with ht
  · exact hf ⟨t.val,ht⟩
  · exact zero_loss_admissible W hG

end Paper254
#print axioms Paper254.prefix_regret
#print axioms Paper254.padded_pathLength
