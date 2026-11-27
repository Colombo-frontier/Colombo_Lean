import AdaptiveSphereReframe
import AdaptiveSphereCoordinateRotations
import PosteriorCenterEnergy

open MeasureTheory
open scoped RealInnerProductSpace

namespace Task006.PosteriorResidualEnergy

open Task006.HaarRebalancing Task006.AdaptiveSphereBlock Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereGeometry
open Task006.AdaptiveSphereReframe Task006.AdaptiveSphereCoordinateRotations Task006.PosteriorCenter
open Task006.AdaptiveSphereAction

noncomputable section
variable {d : ℕ}

theorem prefixPart_block_action (r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d-r)) (x : E d) :
    prefixPart r (action (blockOrthogonal d r hr g) x) = prefixPart r x := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i.val < r
  · simp only [prefixPart,WithLp.ofLp_toLp,if_pos hi]
    exact blockOrthogonal_action_prefix r hr g x i hi
  · simp [prefixPart,hi]

theorem reframe_projectedCenter (state : FrameState d) (H : ResidualControls d) (θ : E d) :
    projectedCenter (reframe state H) θ = projectedCenter state θ := by
  rw [projectedCenter_eq_sum,projectedCenter_eq_sum]
  dsimp only [reframe]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j.val < state.1.val := (Finset.mem_filter.mp hj).2
  have hfix : frameVector (state.2 * blockOrthogonal d state.1.val (by omega) (H state.1)) j =
      frameVector state.2 j := by
    rw [frameVector,action_mul]
    have hb := blockOrthogonal_fixed_first d state.1.val (by omega) (H state.1) ⟨j.val,hjr⟩
    rw [indexSplit_first_eq d state.1.val (by omega) j hjr] at hb
    rw [hb]
    rfl
  rw [hfix]

theorem norm_sq_split (r : ℕ) (hr : r ≤ d) (x : E d) :
    ‖x‖^2 =
      (∑ i : Fin r, x (indexSplit d r hr (Sum.inl i))^2) +
      ‖residualCoordinates r hr x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,← (indexSplit d r hr).sum_comp,Fintype.sum_sum_type,
    EuclideanSpace.real_norm_sq_eq]
  rfl

theorem prefixPart_norm_sq (r : ℕ) (hr : r ≤ d) (x : E d) :
    ‖prefixPart r x‖^2 = ∑ i : Fin r, x (indexSplit d r hr (Sum.inl i))^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,← (indexSplit d r hr).sum_comp,Fintype.sum_sum_type]
  have hl : (∑ i : Fin r, (prefixPart r x (indexSplit d r hr (Sum.inl i)))^2) =
      ∑ i : Fin r, x (indexSplit d r hr (Sum.inl i))^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hv := indexSplit_left_val d r hr i
    simp [prefixPart,hv,i.isLt]
  have hz : (∑ i : Fin (d-r), (prefixPart r x (indexSplit d r hr (Sum.inr i)))^2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hv := indexSplit_right_val d r hr i
    have hn : ¬ (indexSplit d r hr (Sum.inr i)).val < r := by omega
    simp [prefixPart,hn]
  rw [hl,hz,add_zero]

theorem residualCoordinates_norm_sq (r : ℕ) (hr : r ≤ d) (x : E d) :
    ‖residualCoordinates r hr x‖^2 = ‖x‖^2-‖prefixPart r x‖^2 := by
  rw [norm_sq_split r hr x,prefixPart_norm_sq r hr x]
  ring

end
end Task006.PosteriorResidualEnergy
