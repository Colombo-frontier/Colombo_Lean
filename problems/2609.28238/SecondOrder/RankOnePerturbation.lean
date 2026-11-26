import SecondOrder.EuclideanCoordinates

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def rankOneMap (u : E) : E →L[ℝ] E := (InnerProductSpace.toDual ℝ E u).smulRight u

theorem rankOneMap_sub (u v : E) :
    rankOneMap u-rankOneMap v =
      (InnerProductSpace.toDual ℝ E u).smulRight (u-v)+
      (InnerProductSpace.toDual ℝ E (u-v)).smulRight v := by
  ext w
  simp [rankOneMap, inner_sub_left, smul_sub, sub_smul]

theorem rankOneMap_sub_norm (u v : E) :
    ‖rankOneMap u-rankOneMap v‖ ≤ (‖u‖+‖v‖)*‖u-v‖ := by
  rw [rankOneMap_sub]
  have h := norm_add_le ((InnerProductSpace.toDual ℝ E u).smulRight (u-v))
    ((InnerProductSpace.toDual ℝ E (u-v)).smulRight v)
  simp only [ContinuousLinearMap.norm_smulRight_apply, LinearIsometryEquiv.norm_map] at h
  convert h using 1 <;> ring

theorem diagonalMap_sub {d : ℕ} (u v : Point d) : diagonalMap u-diagonalMap v = diagonalMap (u-v) := by
  ext w i
  simp [sub_mul]

end
end SecondOrder
