import AnytimePartition254
import UpperMain254

noncomputable section
open scoped BigOperators
namespace Paper254

def anytimeRestriction {d : ℕ} {D : ℝ} {W : Domain d D}
    (A : (t : ℕ) → (Fin t → Loss d) → W.carrier) (T : ℕ) : OnlineLearner W T :=
  fun t history => A t.val history

def epochLoss {d T : ℕ} (f : Fin T → Loss d) (j : Fin (epochCount T)) :
    Fin (epochLength T j.val) → Loss d := fun k => f (epochRound ⟨j,k⟩)

theorem doubling_epoch_prediction {d T : ℕ} {D : ℝ} {W : Domain d D}
    (family : (H : ℕ) → OnlineLearner W H) (f : Fin T → Loss d)
    (j : Fin (epochCount T)) (k : Fin (epochLength T j.val)) :
    predictions (anytimeRestriction (doublingLearner family) T) f (epochRound ⟨j,k⟩)=
      predictions (prefixLearner (family (2^j.val)) (min_le_left _ _)) (epochLoss f j) k := by
  have hH : doublingHorizon (epochRound ⟨j,k⟩).val=2^j.val := by
    rw [doublingHorizon,epochRound_log]
  have hs : doublingStart (epochRound ⟨j,k⟩).val=2^j.val-1 := by rw [doublingStart,hH]
  have hoff : (epochRound ⟨j,k⟩).val-doublingStart (epochRound ⟨j,k⟩).val=k.val := by
    rw [hs]; dsimp [epochRound]; omega
  have hlog : doublingEpoch (2^j.val-1+k.val)=j.val := epochRound_log ⟨j,k⟩
  unfold predictions anytimeRestriction doublingLearner prefixLearner
  dsimp only
  simp only [doublingHorizon,doublingStart,epochRound,hlog,Nat.add_sub_cancel_left]
  congr 1
  · apply (Fin.heq_ext_iff hH).mpr
    exact hoff
  · apply Function.hfunext (congrArg Fin hoff)
    intro x y hxy
    apply heq_of_eq
    have hv := Fin.val_eq_val_of_heq hxy
    unfold past epochLoss
    congr 1
    apply Fin.ext
    dsimp [epochRound]
    omega

theorem doubling_regret_decomposition {d T : ℕ} {D : ℝ} {W : Domain d D}
    (family : (H : ℕ) → OnlineLearner W H) (f : Fin T → Loss d) (u : Fin T → W.carrier) :
    regret (anytimeRestriction (doublingLearner family) T) f u =
      ∑ j : Fin (epochCount T),regret (prefixLearner (family (2^j.val))
        (min_le_left _ _)) (epochLoss f j) (epochComparator u j) := by
  unfold regret
  rw [← sum_epochs]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [doubling_epoch_prediction]
  rfl

/-- The fixed-horizon statistical theorem supplies a single family whose
every prefix is valid. Future losses are zero; the comparator is held fixed. -/
theorem upper_family_prefix (D G η : ℝ) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) :
    ∃ C : ℝ,0 < C ∧ ∀ d : ℕ,0 < d → ∀ W : Domain d D,
    ∃ family : (H : ℕ) → OnlineLearner W H,
      ∀ H m : ℕ,0 < m → ∀ hm : m ≤ H, ∀ f : Fin m → Loss d,
      (∀ t,AdmissibleLoss W G η (f t)) → ∀ u : Fin m → W.carrier,
      regret (prefixLearner (family H) hm) f u ≤ C*upperFrontier d H (pathLength u) := by
  obtain ⟨C,hC,hmain⟩ := main_upper D G η hD hG hη
  refine ⟨C,hC,?_⟩
  intro d hd W
  have hex : ∀ H : ℕ,∃ A : OnlineLearner W H,
      ∀ f : Fin H → Loss d,(∀ t,AdmissibleLoss W G η (f t)) →
      ∀ u : Fin H → W.carrier,regret A f u ≤ C*upperFrontier d H (pathLength u) := by
    intro H
    by_cases hH : 0 < H
    · exact hmain d H hd hH W
    · have he : H=0 := by omega
      subst H
      refine ⟨fun t => Fin.elim0 t,?_⟩
      intro f hf u
      simp [regret,upperFrontier,curvedRate,pathLength,logFactor]
      positivity
  choose family hfamily using hex
  refine ⟨family,?_⟩
  intro H m hm0 hm f hf u
  have hh := hfamily H (paddedLoss f) (padded_admissible W hG.le f hf) (paddedComparator hm0 u)
  rw [prefix_regret (family H) hm hm0 f u,padded_pathLength hm hm0 u] at hh
  exact hh

end Paper254
#print axioms Paper254.doubling_regret_decomposition
#print axioms Paper254.upper_family_prefix
