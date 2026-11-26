import AdaptiveSphereDegeneratePosterior

/-! The explicit Gram--Schmidt frame spans exactly the linear information
supplied by the queried vectors. This identifies the posterior fiber's frame
notation with the manuscript's actual measurement span. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereSpan
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereKernel
noncomputable section
variable {d : ℕ}

def frameSpan (state : FrameState d) : Submodule ℝ (E d) :=
  Submodule.span ℝ (frameVector state.2 '' {j : Fin d | j.val < state.1.val})

theorem frameVector_mem_frameSpan (state : FrameState d) (j : Fin d) (hj : j.val < state.1.val) :
    frameVector state.2 j ∈ frameSpan state := Submodule.subset_span ⟨j,hj,rfl⟩

theorem frameSpan_le {T : Submodule ℝ (E d)} (state : FrameState d)
    (hgen : ∀ j : Fin d, j.val < state.1.val → frameVector state.2 j ∈ T) :
    frameSpan state ≤ T := by
  apply Submodule.span_le.mpr
  rintro x ⟨j,hj,rfl⟩
  exact hgen j hj

theorem projectedCenter_mem_frameSpan (state : FrameState d) (θ : E d) :
    projectedCenter state θ ∈ frameSpan state := by
  rw [projectedCenter_eq_sum]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (frameVector_mem_frameSpan state j (Finset.mem_filter.mp hj).2)

theorem frameSpan_full_rank (state : FrameState d) (hr : state.1.val=d) : frameSpan state = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  rw [← projectedCenter_full_rank state hr x]
  exact projectedCenter_mem_frameSpan state x

theorem liftResidual_zero (r : ℕ) (hr : r ≤ d) : liftResidual r hr (0 : E (d-r)) = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i.val < r <;> simp [liftResidual,hi]

theorem query_mem_frameSpan_of_zero_residual (state : FrameState d) (q : E d)
    (hz : residualCoordinates state.1.val (by omega) (action state.2⁻¹ q) = 0) :
    q ∈ frameSpan state := by
  have h := congrArg (action state.2) (coordinate_decomposition state.1.val (by omega) (action state.2⁻¹ q))
  rw [hz,liftResidual_zero,add_zero,action_inverse_cancel] at h
  rw [h]
  exact projectedCenter_mem_frameSpan state q

/-- Exact information-span update, including dependent queries and full rank. -/
theorem frameSpan_stateStep_full (state : FrameState d) (q : E d) :
    frameSpan (stateStep d le_rfl state q) = frameSpan state ⊔ Submodule.span ℝ {q} := by
  by_cases hr : state.1.val < d
  · let r : Fin d := ⟨state.1.val,hr⟩
    by_cases hz : residualCoordinates state.1.val (by omega) (action state.2⁻¹ q) = 0
    · have hs : stateStep d le_rfl state q = state := by simp only [stateStep,dif_pos hr,if_pos hz]
      rw [hs]
      apply le_antisymm le_sup_left
      exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem q _).mpr
        (query_mem_frameSpan_of_zero_residual state q hz))
    · let next : FrameState d := (⟨r.val+1,by omega⟩,residualUpdate r state.2 q)
      have hs : stateStep d le_rfl state q = next := by
        simp only [stateStep,dif_pos hr,if_neg hz,next,r]
      rw [hs]
      have old_le : frameSpan state ≤ frameSpan next := by
        apply frameSpan_le
        intro j hj
        have hkeep := residualUpdate_keeps_prefix r state.2 q j hj
        rw [← hkeep]
        exact frameVector_mem_frameSpan next j (by change j.val<state.1.val+1; omega)
      let v := frameVector (residualUpdate r state.2 q) r
      have hvnew : v ∈ frameSpan next := frameVector_mem_frameSpan next r (Nat.lt_succ_self r.val)
      have hdecomp : q = projectedCenter state q +
          ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) (action state.2⁻¹ q)‖ • v :=
        query_decomposition_ambient r state.2 q hz
      have hqnew : q ∈ frameSpan next := by
        rw [hdecomp]
        exact Submodule.add_mem _ (old_le (projectedCenter_mem_frameSpan state q))
          (Submodule.smul_mem _ _ hvnew)
      have hnorm : ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) (action state.2⁻¹ q)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hz
      have hvrep : v = ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) (action state.2⁻¹ q)‖⁻¹ •
          (q-projectedCenter state q) := by
        have hdiff : q-projectedCenter state q =
            ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) (action state.2⁻¹ q)‖ • v := by
          exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hdecomp)
        rw [hdiff,smul_smul,inv_mul_cancel₀ hnorm,one_smul]
      have hvold : v ∈ frameSpan state ⊔ Submodule.span ℝ {q} := by
        rw [hvrep]
        apply Submodule.smul_mem
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self q))
          (Submodule.mem_sup_left (projectedCenter_mem_frameSpan state q))
      apply le_antisymm
      · apply frameSpan_le
        intro j hj
        by_cases hjr : j.val<r.val
        · have hkeep := residualUpdate_keeps_prefix r state.2 q j hjr
          change frameVector (residualUpdate r state.2 q) j ∈ _
          rw [hkeep]
          exact Submodule.mem_sup_left (frameVector_mem_frameSpan state j hjr)
        · have hje : j=r := Fin.ext (by change j.val<r.val+1 at hj; omega)
          subst j
          exact hvold
      · exact sup_le old_le ((Submodule.span_singleton_le_iff_mem q _).mpr hqnew)
  · have hfull : state.1.val=d := by omega
    have hs : stateStep d le_rfl state q = state := by simp only [stateStep,dif_neg hr]
    rw [hs,frameSpan_full_rank state hfull,top_sup_eq]

#print axioms frameSpan_stateStep_full
end
end Task006.AdaptiveSphereSpan
