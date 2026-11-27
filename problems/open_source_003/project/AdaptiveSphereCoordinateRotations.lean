import AdaptiveSphereGeometry
import PosteriorCenterCore

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereCoordinateRotations
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter
noncomputable section
variable {d : ℕ}

def negativeOrthogonal (n : ℕ) : OrthogonalGroup n :=
  orthogonalMatrixOfLinearIsometryEquiv (LinearIsometryEquiv.neg ℝ : E n ≃ₗᵢ[ℝ] E n)

theorem negativeOrthogonal_action (n : ℕ) (x : E n) :
    action (negativeOrthogonal n) x = -x := by
  rw [negativeOrthogonal, action_matrixOfIsometry]
  rfl

theorem negativeOrthogonal_entry (n : ℕ) (i j : Fin n) :
    (negativeOrthogonal n : Matrix (Fin n) (Fin n) ℝ) i j =
      -(if i=j then 1 else 0) := by
  change (LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (LinearIsometryEquiv.neg ℝ : E n ≃ₗᵢ[ℝ] E n).toLinearMap) i j = _
  rw [LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem blockOrthogonal_action_prefix (r : ℕ) (hr : r ≤ d)
    (g : OrthogonalGroup (d-r)) (x : E d) (i : Fin d) (hi : i.val < r) :
    (action (blockOrthogonal d r hr g) x) i = x i := by
  change (∑ j : Fin d, (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ) i j * x j) = _
  rw [Finset.sum_eq_single i]
  · rw [blockOrthogonal_apply]
    simp [hi]
  · intro j hj hji
    rw [blockOrthogonal_apply]
    by_cases hjr : j.val < r
    · simp [hjr,Ne.symm hji]
    · simp [hjr,hi]
  · simp

theorem blockOrthogonal_action_residual (r : ℕ) (hr : r ≤ d)
    (g : OrthogonalGroup (d-r)) (x : E d) :
    residualCoordinates r hr (action (blockOrthogonal d r hr g) x) =
      action g (residualCoordinates r hr x) := by
  apply WithLp.ofLp_injective 2
  funext i
  change (∑ j : Fin d,
      (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ)
        (indexSplit d r hr (Sum.inr i)) j * x j) =
    ∑ j : Fin (d-r), (g : Matrix (Fin (d-r)) (Fin (d-r)) ℝ) i j *
      x (indexSplit d r hr (Sum.inr j))
  rw [← (indexSplit d r hr).sum_comp]
  rw [Fintype.sum_sum_type]
  have hleft : (∑ j : Fin r,
      (blockOrthogonal d r hr g : Matrix (Fin d) (Fin d) ℝ)
        (indexSplit d r hr (Sum.inr i)) (indexSplit d r hr (Sum.inl j)) *
          x (indexSplit d r hr (Sum.inl j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [blockOrthogonal_entry_first]
    simp
  rw [hleft,zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  rw [blockOrthogonal_entry_residual]

/-- The residual negation leaves the measured prefix fixed and reverses its
orthogonal complement, including degenerate zero-dimensional complements. -/
theorem blockNegative_action (r : ℕ) (hr : r ≤ d) (x : E d) :
    action (blockOrthogonal d r hr (negativeOrthogonal (d-r))) x =
      (2 : ℝ) • prefixPart r x - x := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i.val < r
  · have h := blockOrthogonal_action_prefix r hr (negativeOrthogonal (d-r)) x i hi
    change (action (blockOrthogonal d r hr (negativeOrthogonal (d-r))) x) i = _
    rw [h]
    simp [prefixPart,hi]
    ring
  · let j : Fin (d-r) := ⟨i.val-r,by omega⟩
    have he : indexSplit d r hr (Sum.inr j) = i := by
      exact indexSplit_residual_eq d r hr i hi
    have h := congrArg (fun y : E (d-r) => y j)
      (blockOrthogonal_action_residual r hr (negativeOrthogonal (d-r)) x)
    rw [negativeOrthogonal_action] at h
    change (action (blockOrthogonal d r hr (negativeOrthogonal (d-r))) x) i = _
    change (action (blockOrthogonal d r hr (negativeOrthogonal (d-r))) x)
        (indexSplit d r hr (Sum.inr j)) = -x (indexSplit d r hr (Sum.inr j)) at h
    rw [he] at h
    rw [h]
    simp [prefixPart,hi]

#print axioms negativeOrthogonal_action
#print axioms negativeOrthogonal_entry
#print axioms blockOrthogonal_action_prefix
#print axioms blockOrthogonal_action_residual
#print axioms blockNegative_action
end
end Task006.AdaptiveSphereCoordinateRotations
