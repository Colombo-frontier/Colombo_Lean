import AdaptiveSphereState
import AdaptiveSphereGeometry

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.PosteriorCenter

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereState
open Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereGeometry

noncomputable section
variable {d : ℕ}

def projectedCenter (state : FrameState d) (θ : E d) : E d :=
  action state.2 (prefixPart state.1.val (action state.2⁻¹ θ))

def frameVector (B : OrthogonalGroup d) (j : Fin d) : E d :=
  action B ((EuclideanSpace.basisFun (Fin d) ℝ) j)

theorem coordinate_as_inner (B : OrthogonalGroup d) (θ : E d) (j : Fin d) :
    (action B⁻¹ θ) j = inner ℝ θ (frameVector B j) := by
  rw [← EuclideanSpace.inner_basisFun_real]
  have h := (action B).inner_map_map (action B⁻¹ θ)
    ((EuclideanSpace.basisFun (Fin d) ℝ) j)
  rw [action_inverse_cancel] at h
  exact h.symm

theorem projectedCenter_eq_sum (state : FrameState d) (θ : E d) :
    projectedCenter state θ = ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < state.1.val),
      (inner ℝ θ (frameVector state.2 j)) • frameVector state.2 j := by
  rw [projectedCenter,prefixPart_eq_sum,map_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j.val < state.1.val
  · simp only [if_pos h,map_smul,coordinate_as_inner,frameVector]
  · simp only [if_neg h,map_zero]

theorem projectedCenter_self_adjoint (state : FrameState d) (θ q : E d) :
    inner ℝ (projectedCenter state θ) q = inner ℝ θ (projectedCenter state q) := by
  rw [projectedCenter_eq_sum,projectedCenter_eq_sum,sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_left,inner_smul_right,real_inner_comm (frameVector state.2 j) q]
  simp only [conj_trivial]
  ring

theorem projectedCenter_rank_increment (r : Fin d) (B B' : OrthogonalGroup d)
    (hfix : ∀ j : Fin d, j.val < r.val → frameVector B' j = frameVector B j)
    (θ : E d) :
    projectedCenter (⟨r.val+1,by omega⟩,B') θ =
      projectedCenter (⟨r.val,by omega⟩,B) θ +
        inner ℝ θ (frameVector B' r) • frameVector B' r := by
  classical
  have hs : Finset.univ.filter (fun j : Fin d => j.val < r.val+1) =
      insert r (Finset.univ.filter (fun j : Fin d => j.val < r.val)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro hj
      by_cases he : j.val = r.val
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | hj) <;> omega
  rw [projectedCenter_eq_sum,projectedCenter_eq_sum]
  dsimp only
  rw [hs,Finset.sum_insert (by simp),add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hfix j (Finset.mem_filter.mp hj).2]

theorem residualUpdate_keeps_prefix (r : Fin d) (B : OrthogonalGroup d) (q : E d)
    (j : Fin d) (hj : j.val < r.val) :
    frameVector (residualUpdate r B q) j = frameVector B j := by
  simp only [frameVector,residualUpdate,action_mul,fullResidualStep_fixes_prefix r _ j hj]

theorem query_decomposition_ambient (r : Fin d) (B : OrthogonalGroup d) (q : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) (action B⁻¹ q) ≠ 0) :
    q = projectedCenter (⟨r.val,by omega⟩,B) q +
      ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) (action B⁻¹ q)‖ •
        frameVector (residualUpdate r B q) r := by
  have h := congrArg (action B) (query_decomposition r (action B⁻¹ q) hx)
  simpa only [action_inverse_cancel,map_add,map_smul,projectedCenter,frameVector,
    residualUpdate,action_mul] using h

theorem projectedCenter_update (r : Fin d) (B : OrthogonalGroup d) (q θ : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) (action B⁻¹ q) ≠ 0) :
    projectedCenter (⟨r.val+1,by omega⟩,residualUpdate r B q) θ =
      projectedCenter (⟨r.val,by omega⟩,B) θ +
        ((inner ℝ θ q - inner ℝ (projectedCenter (⟨r.val,by omega⟩,B) θ) q) /
          ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) (action B⁻¹ q)‖) •
            frameVector (residualUpdate r B q) r := by
  rw [projectedCenter_rank_increment r B _ (residualUpdate_keeps_prefix r B q)]
  congr 1
  congr 1
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).2
  rw [projectedCenter_self_adjoint]
  have h := congrArg (fun v => inner ℝ θ v) (query_decomposition_ambient r B q hx)
  rw [inner_add_right,inner_smul_right] at h
  linarith

end
end Task006.PosteriorCenter
