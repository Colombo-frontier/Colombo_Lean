import AdaptiveSphereSpan

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereSpan
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereResidualFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter
noncomputable section
variable {d : ℕ}

theorem prefixPart_fixes_basis (r : ℕ) (j : Fin d) (hj : j.val<r) :
    prefixPart r ((EuclideanSpace.basisFun (Fin d) ℝ) j) =
      (EuclideanSpace.basisFun (Fin d) ℝ) j := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i.val<r
  · simp [prefixPart,hi]
  · have hne : i≠j := by intro he; subst i; exact hi hj
    simp [prefixPart,hi,EuclideanSpace.basisFun_apply,Ne.symm hne]

theorem projectedCenter_fixes_prefix (state : FrameState d) (j : Fin d) (hj : j.val<state.1.val) :
    projectedCenter state (frameVector state.2 j) = frameVector state.2 j := by
  rw [projectedCenter,frameVector,action_inverse_cancel_left,prefixPart_fixes_basis _ j hj]

theorem projectedCenter_residual_mem_orthogonal (state : FrameState d) (θ : E d) :
    θ-projectedCenter state θ ∈ (frameSpan state).orthogonal := by
  have hle : frameSpan state ≤ LinearMap.ker ((innerSL ℝ (θ-projectedCenter state θ)).toLinearMap) := by
    apply frameSpan_le
    intro j hj
    change inner ℝ (θ-projectedCenter state θ) (frameVector state.2 j) = 0
    rw [inner_sub_left,projectedCenter_self_adjoint,projectedCenter_fixes_prefix state j hj,sub_self]
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro x hx
  exact hle hx

/-- The concrete transcript center is exactly the ordinary orthogonal projector
onto the generated frame span. -/
theorem frameSpan_starProjection (state : FrameState d) (θ : E d) :
    (frameSpan state).starProjection θ = projectedCenter state θ :=
  Submodule.eq_starProjection_of_mem_orthogonal
    (projectedCenter_mem_frameSpan state θ) (projectedCenter_residual_mem_orthogonal state θ)

def prefixIndex (r : ℕ) (hr : r ≤ d) (i : Fin r) : Fin d := ⟨i.val,by omega⟩

theorem prefixIndex_injective (r : ℕ) (hr : r ≤ d) : Function.Injective (prefixIndex (d := d) r hr) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin d => x.val) hij)

theorem frameSpan_eq_span_prefix (state : FrameState d) :
    frameSpan state = Submodule.span ℝ (Set.range (fun i : Fin state.1.val =>
      frameVector state.2 (prefixIndex state.1.val (by omega) i))) := by
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨j.val,hj⟩,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨prefixIndex state.1.val (by omega) i,i.isLt,rfl⟩

/-- The maintained rank equals the actual dimension of its orthonormal span. -/
theorem frameSpan_finrank (state : FrameState d) : Module.finrank ℝ (frameSpan state) = state.1.val := by
  have horth : Orthonormal ℝ (frameVector state.2) := by
    rw [orthonormal_iff_ite]
    exact frameVector_inner state.2
  have hli := (horth.comp (prefixIndex state.1.val (by omega))
    (prefixIndex_injective state.1.val (by omega))).linearIndependent
  have hli' : LinearIndependent ℝ (fun i : Fin state.1.val =>
      frameVector state.2 (prefixIndex state.1.val (by omega) i)) := by
    simpa only [Function.comp_def] using hli
  rw [frameSpan_eq_span_prefix,finrank_span_eq_card hli',Fintype.card_fin]

#print axioms frameSpan_starProjection
#print axioms frameSpan_finrank
end
end Task006.AdaptiveSphereSpan
