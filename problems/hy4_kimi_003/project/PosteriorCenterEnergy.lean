import PosteriorCenterCore
import LowerAudit

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.PosteriorCenter

open Task006.HaarRebalancing Task006.AdaptiveSphereState Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereGeometry

noncomputable section
variable {d : ℕ}

theorem frameVector_inner (B : OrthogonalGroup d) (i j : Fin d) :
    inner ℝ (frameVector B i) (frameVector B j) = if i = j then 1 else 0 := by
  rw [frameVector,frameVector,(action B).inner_map_map]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal i j

theorem frameVector_norm (B : OrthogonalGroup d) (j : Fin d) : ‖frameVector B j‖ = 1 := by
  rw [frameVector,(action B).norm_map]
  exact (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one j

theorem prefixPart_norm_le (r : ℕ) (x : E d) : ‖prefixPart r x‖ ≤ ‖x‖ := by
  have hsq : ‖prefixPart r x‖^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjr : j.val < r
    · simp [prefixPart,hjr]
    · simpa [prefixPart,hjr] using sq_nonneg (x j)
  nlinarith [norm_nonneg (prefixPart r x),norm_nonneg x]

theorem projectedCenter_norm_le (state : FrameState d) (θ : E d) :
    ‖projectedCenter state θ‖ ≤ ‖θ‖ := by
  rw [projectedCenter,(action state.2).norm_map]
  exact (prefixPart_norm_le _ _).trans_eq ((action state.2⁻¹).norm_map θ)

theorem prefixPart_inner_remainder (r : ℕ) (x : E d) :
    inner ℝ (prefixPart r x) (x-prefixPart r x) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjr : j.val < r <;> simp [prefixPart,hjr]

theorem projectedCenter_inner_remainder (state : FrameState d) (θ : E d) :
    inner ℝ (projectedCenter state θ) (θ-projectedCenter state θ) = 0 := by
  have he : θ-projectedCenter state θ =
      action state.2 (action state.2⁻¹ θ - prefixPart state.1.val (action state.2⁻¹ θ)) := by
    rw [map_sub,action_inverse_cancel]
    rfl
  rw [he,projectedCenter,(action state.2).inner_map_map]
  exact prefixPart_inner_remainder _ _

theorem projectedCenter_pythagoras (state : FrameState d) (θ : E d) :
    ‖θ-projectedCenter state θ‖^2 = ‖θ‖^2 - ‖projectedCenter state θ‖^2 := by
  have h := norm_add_sq_real (projectedCenter state θ) (θ-projectedCenter state θ)
  rw [projectedCenter_inner_remainder] at h
  have he : projectedCenter state θ + (θ-projectedCenter state θ) = θ := by abel
  rw [he] at h
  linarith

theorem projectedCenter_orthogonal_new_pivot (r : Fin d) (B : OrthogonalGroup d)
    (q θ : E d) :
    inner ℝ (projectedCenter (⟨r.val,by omega⟩,B) θ)
      (frameVector (residualUpdate r B q) r) = 0 := by
  classical
  rw [projectedCenter_eq_sum,sum_inner]
  apply Finset.sum_eq_zero
  intro j hj
  have hjr : j.val < r.val := (Finset.mem_filter.mp hj).2
  have hne : j ≠ r := by intro he; subst j; omega
  rw [inner_smul_left,← residualUpdate_keeps_prefix r B q j hjr,frameVector_inner]
  simp [hne]

theorem projectedCenter_energy_increment (r : Fin d) (B : OrthogonalGroup d) (q θ : E d) :
    ‖projectedCenter (⟨r.val+1,by omega⟩,residualUpdate r B q) θ‖^2 -
        ‖projectedCenter (⟨r.val,by omega⟩,B) θ‖^2 =
      (inner ℝ θ (frameVector (residualUpdate r B q) r))^2 := by
  rw [projectedCenter_rank_increment r B _ (residualUpdate_keeps_prefix r B q)]
  exact Task006LowerAudit.orthogonal_measurement_energy _ θ _
    (frameVector_norm _ _) (projectedCenter_orthogonal_new_pivot r B q θ)

end
end Task006.PosteriorCenter
