import PosteriorCenterEnergy
import StoppedEnergy

open MeasureTheory
open scoped RealInnerProductSpace

namespace Task006.PosteriorEnergyPartition

open Task006.HaarRebalancing Task006.AdaptiveSphereState Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.PosteriorCenter Task006.StoppedEnergy

noncomputable section
variable {d : ℕ}

def activeRank (state : FrameState d) (q : E d) (k : ℕ) (r : Fin d) : Prop :=
  state.1.val = r.val ∧ r.val < k ∧
    residualCoordinates r.val (Nat.le_of_lt r.isLt) (action state.2⁻¹ q) ≠ 0

local instance (state : FrameState d) (q : E d) (k : ℕ) :
    DecidablePred (activeRank state q k) := fun _ => Classical.propDecidable _

theorem sum_active (state : FrameState d) (q : E d) (k : ℕ) (hkd : k ≤ d)
    (f : Fin d → ℝ) :
    (∑ r : Fin d, if activeRank state q k r then f r else 0) =
      if hr : state.1.val < k then
        let pivot : Fin d := ⟨state.1.val,by omega⟩
        if residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q) = 0
        then 0 else f pivot
      else 0 := by
  classical
  by_cases hr : state.1.val < k
  · rw [dif_pos hr]
    let pivot : Fin d := ⟨state.1.val,by omega⟩
    by_cases hz : residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q) = 0
    · have hn (r : Fin d) : ¬ activeRank state q k r := by
        rintro ⟨hrank,hlt,hnz⟩
        have he : r = pivot := Fin.ext hrank.symm
        subst r
        exact hnz hz
      simp only [hn,if_false]
      dsimp only [pivot] at hz
      simp only [hz,if_pos,Finset.sum_const_zero]
    · have hsum : (∑ r : Fin d, if activeRank state q k r then f r else 0) = f pivot := by
        calc
          _ = (if activeRank state q k pivot then f pivot else 0) := by
            apply Finset.sum_eq_single pivot
            · intro r hr' hne
              have hn : ¬ activeRank state q k r := by
                rintro ⟨hrank,_,_⟩
                exact hne (Fin.ext hrank.symm)
              simp only [hn,if_false]
            · intro hn
              simp at hn
          _ = f pivot := by
            rw [if_pos (show activeRank state q k pivot from ⟨rfl,hr,hz⟩)]
      rw [hsum]
      dsimp only [pivot] at hz ⊢
      rw [if_neg hz]
  · rw [dif_neg hr]
    apply Finset.sum_eq_zero
    intro r hmem
    have hn : ¬ activeRank state q k r := by
      rintro ⟨hrank,hlt,_⟩
      exact hr (by omega)
    simp only [hn,if_false]

theorem energy_increment_partition (state : FrameState d) (q θ : E d) (k : ℕ) (hkd : k ≤ d) :
    ‖projectedCenter (stateStep k hkd state q) θ‖^2 - ‖projectedCenter state θ‖^2 =
      ∑ r : Fin d, if activeRank state q k r then
        (inner ℝ θ (frameVector (stateStep k hkd state q).2 r))^2 else 0 := by
  classical
  rw [sum_active state q k hkd (fun r =>
    (inner ℝ θ (frameVector (stateStep k hkd state q).2 r))^2)]
  by_cases hr : state.1.val < k
  · rw [dif_pos hr]
    let pivot : Fin d := ⟨state.1.val,by omega⟩
    by_cases hz : residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q) = 0
    · dsimp only [pivot] at hz
      simp only [stateStep,dif_pos hr,hz,if_pos,sub_self]
    · dsimp only [pivot] at hz
      simp only [stateStep,dif_pos hr,hz,if_neg,ite_false]
      exact projectedCenter_energy_increment pivot state.2 q θ
  · simp only [stateStep,dif_neg hr,sub_self]

theorem rankPotential_succ (d r : ℕ) :
    rankPotential d (r+1) - rankPotential d r = 1/((d : ℝ)-r) := by
  rw [rankPotential,Finset.sum_range_succ]
  change rankPotential d r + _ - rankPotential d r = _
  ring

theorem potential_increment_partition (state : FrameState d) (q : E d) (k : ℕ) (hkd : k ≤ d) :
    rankPotential d (stateStep k hkd state q).1.val - rankPotential d state.1.val =
      ∑ r : Fin d, if activeRank state q k r then 1/((d : ℝ)-r.val) else 0 := by
  classical
  rw [sum_active state q k hkd (fun r => 1/((d : ℝ)-r.val))]
  by_cases hr : state.1.val < k
  · rw [dif_pos hr]
    let pivot : Fin d := ⟨state.1.val,by omega⟩
    by_cases hz : residualCoordinates pivot.val (Nat.le_of_lt pivot.isLt) (action state.2⁻¹ q) = 0
    · dsimp only [pivot] at hz
      simp only [stateStep,dif_pos hr,hz,if_pos,sub_self]
    · dsimp only [pivot] at hz
      simp only [stateStep,dif_pos hr,hz,if_neg,ite_false]
      exact rankPotential_succ d state.1.val
  · simp only [stateStep,dif_neg hr,sub_self]

end
end Task006.PosteriorEnergyPartition
