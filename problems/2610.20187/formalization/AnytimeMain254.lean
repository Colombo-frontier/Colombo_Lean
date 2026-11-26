import AnytimeLearner254
import AnytimeFrontier254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem epoch_horizon_le {T : ℕ} (hT : 0 < T) (j : Fin (epochCount T)) : 2^j.val ≤ T := by
  have hj : j.val ≤ Nat.log 2 T := by have := j.isLt; dsimp [epochCount] at this; omega
  exact (Nat.pow_le_pow_right (by omega : 0 < 2) hj).trans (Nat.pow_log_le_self 2 hT.ne')

theorem epoch_upperFrontier_sum {d T : ℕ} {D : ℝ} {W : Domain d D}
    (hT : 0 < T) (u : Fin T → W.carrier) :
    (∑ j : Fin (epochCount T),upperFrontier d (2^j.val) (pathLength (epochComparator u j))) ≤
      anytimeFrontier d T (pathLength u) := by
  let H : Fin (epochCount T) → ℝ := fun j => (2^j.val : ℕ)
  let P := fun j : Fin (epochCount T) => pathLength (epochComparator u j)
  let a : ℝ := d*logFactor T^2
  let b : ℝ := (d:ℝ)^(1/3:ℝ)*logFactor T^(4/3:ℝ)
  have hL : 0 ≤ logFactor T := (by norm_num : (0:ℝ) ≤ 1).trans (logFactor_ge_one T hT)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hP : ∀ j,0 ≤ P j := fun j => pathLength_nonneg _
  have hH : ∀ j,0 ≤ H j := fun j => Nat.cast_nonneg _
  have hsumH : (∑ j,H j) ≤ 2*T := by
    dsimp [H]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [Fin.sum_univ_eq_sum_range]
    exact doubling_planned_time T hT
  have hsumP : (∑ j,P j) ≤ pathLength u := epoch_path_sum u
  have henvelope : (∑ j : Fin (epochCount T),upperFrontier d (2^j.val) (P j)) ≤
      ∑ j : Fin (epochCount T),(a+min (b*(H j)^(1/3:ℝ)*(P j)^(2/3:ℝ))
        (min (Real.sqrt (H j*(1+P j))) (H j))) := by
    apply Finset.sum_le_sum
    intro j _
    exact upperFrontier_log_envelope d (2^j.val) T (P j) (by positivity) (epoch_horizon_le hT j) (hP j)
  have hsum := epoch_frontier_sum Finset.univ H P a b hb (fun j _ => hH j) (fun j _ => hP j)
  apply henvelope.trans
  apply hsum.trans
  simp only [Finset.card_univ,Fintype.card_fin]
  have hS : 0 ≤ ∑ j,H j := Finset.sum_nonneg (fun j _ => hH j)
  have hQ : 0 ≤ ∑ j,P j := Finset.sum_nonneg (fun j _ => hP j)
  unfold anytimeFrontier
  dsimp [a,b]
  simp only [epochCount,Nat.cast_add,Nat.cast_one]
  rw [mul_assoc (Nat.log 2 T+1 : ℝ) (d:ℝ) (logFactor T^2)]
  gcongr <;> assumption

/-- A single proper causal learner, chosen before the terminal horizon,
achieves all three dynamic branches with the displayed doubling overhead. -/
def AnytimeUpperStatement : Prop :=
  ∀ D G η : ℝ,0 < D → 0 < G → 0 < η →
  ∃ C : ℝ,0 < C ∧ ∀ d : ℕ,0 < d → ∀ W : Domain d D,
  ∃ A : (t : ℕ) → (Fin t → Loss d) → W.carrier,
  ∀ T : ℕ,0 < T → ∀ f : Fin T → Loss d,
  (∀ t,AdmissibleLoss W G η (f t)) → ∀ u : Fin T → W.carrier,
  regret (anytimeRestriction A T) f u ≤ C*anytimeFrontier d T (pathLength u)

theorem main_anytime_upper : AnytimeUpperStatement := by
  intro D G η hD hG hη
  obtain ⟨C,hC,hfamily⟩ := upper_family_prefix D G η hD hG hη
  refine ⟨C,hC,?_⟩
  intro d hd W
  obtain ⟨family,hprefix⟩ := hfamily d hd W
  refine ⟨doublingLearner family,?_⟩
  intro T hT f hf u
  rw [doubling_regret_decomposition]
  calc
    _ ≤ ∑ j : Fin (epochCount T),C*upperFrontier d (2^j.val) (pathLength (epochComparator u j)) := by
      apply Finset.sum_le_sum
      intro j _
      exact hprefix (2^j.val) (epochLength T j.val) (epoch_length_pos hT j) (min_le_left _ _)
        (epochLoss f j) (fun k => hf (epochRound ⟨j,k⟩)) (epochComparator u j)
    _ = C*∑ j : Fin (epochCount T),upperFrontier d (2^j.val) (pathLength (epochComparator u j)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (epoch_upperFrontier_sum hT u) hC.le

end Paper254
#print axioms Paper254.main_anytime_upper
