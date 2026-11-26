import AnytimeRates254
import FinitePrefix254

noncomputable section
open scoped BigOperators
namespace Paper254

def epochCount (T : ℕ) := Nat.log 2 T+1
def epochLength (T j : ℕ) := min (2^j) (T-(2^j-1))
abbrev EpochRound (T : ℕ) := (j : Fin (epochCount T)) × Fin (epochLength T j.val)

def epochRound {T : ℕ} (e : EpochRound T) : Fin T :=
  ⟨2^e.1.val-1+e.2.val,by
    have hk := e.2.isLt
    dsimp [epochLength] at hk
    omega⟩

theorem epochRound_log {T : ℕ} (e : EpochRound T) :
    doublingEpoch (epochRound e).val=e.1.val := by
  have hp : 0 < 2^e.1.val := by positivity
  have hk : e.2.val < 2^e.1.val := lt_of_lt_of_le e.2.isLt (min_le_left _ _)
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · dsimp [epochRound]; omega
  · change 2^e.1.val-1+e.2.val+1 < 2^(e.1.val+1)
    rw [pow_succ]
    omega

theorem epochRound_bijective (T : ℕ) : Function.Bijective (@epochRound T) := by
  constructor
  · intro e f he
    have hj : e.1=f.1 := Fin.ext (by rw [← epochRound_log e,← epochRound_log f,he])
    cases e with
    | mk j k =>
      cases f with
      | mk j' k' =>
        dsimp at hj
        subst j'
        have hk : k=k' := by
          apply Fin.ext
          have hval := congrArg Fin.val he
          dsimp [epochRound] at hval
          omega
        subst k'
        rfl
  · intro t
    let j : Fin (epochCount T) := ⟨doublingEpoch t.val,by
      have h := Nat.log_mono_right (show t.val+1 ≤ T by omega) (b := 2)
      dsimp [doublingEpoch,epochCount]
      omega⟩
    have hb := doubling_bounds t.val
    let k : Fin (epochLength T j.val) := ⟨t.val-doublingStart t.val,by
      dsimp [epochLength,j]
      apply lt_min
      · exact hb.2.2
      · have ht := t.isLt
        change t.val-doublingStart t.val < T-doublingStart t.val
        omega⟩
    refine ⟨⟨j,k⟩,?_⟩
    apply Fin.ext
    change doublingStart t.val+(t.val-doublingStart t.val)=t.val
    omega

theorem sum_epochs {T : ℕ} (f : Fin T → ℝ) :
    (∑ j : Fin (epochCount T),∑ k : Fin (epochLength T j.val),f (epochRound ⟨j,k⟩))=∑ t,f t := by
  simpa only [Fintype.sum_sigma] using
    (Equiv.ofBijective epochRound (epochRound_bijective T)).sum_comp f

theorem epoch_length_pos {T : ℕ} (hT : 0 < T) (j : Fin (epochCount T)) :
    0 < epochLength T j.val := by
  have hj : j.val ≤ Nat.log 2 T := by have := j.isLt; dsimp [epochCount] at this; omega
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hj
  have h := Nat.pow_log_le_self 2 hT.ne'
  have hpow : 0 < 2^j.val := by positivity
  dsimp [epochLength]
  omega

def epochComparator {d T : ℕ} {D : ℝ} {W : Domain d D}
    (u : Fin T → W.carrier) (j : Fin (epochCount T)) : Fin (epochLength T j.val) → W.carrier :=
  fun k => u (epochRound ⟨j,k⟩)

theorem epoch_path_sum {d T : ℕ} {D : ℝ} {W : Domain d D} (u : Fin T → W.carrier) :
    (∑ j : Fin (epochCount T),pathLength (epochComparator u j)) ≤ pathLength u := by
  let p : Fin T → ℝ := fun t => if ht : 0 < t.val then
    ‖(u t).val-(u ⟨t.val-1,by omega⟩).val‖ else 0
  change _ ≤ ∑ t,p t
  rw [← sum_epochs p]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : 0 < k.val
  · have ht : 0 < (epochRound ⟨j,k⟩).val := by dsimp [epochRound]; omega
    dsimp [pathLength,epochComparator]
    rw [dif_pos hk]
    dsimp [p]
    rw [dif_pos ht]
    have he : epochRound ⟨j,⟨k.val-1,by omega⟩⟩ =
        (⟨(epochRound ⟨j,k⟩).val-1,by have := (epochRound ⟨j,k⟩).isLt; omega⟩ : Fin T) := by
      apply Fin.ext
      dsimp [epochRound]
      omega
    rw [he]
  · dsimp [pathLength]
    rw [dif_neg hk]
    dsimp [p]
    split_ifs <;> positivity

end Paper254
#print axioms Paper254.epochRound_bijective
#print axioms Paper254.epoch_path_sum
