import AdaptiveSphereResidualFrame

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereGeometry

open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame

noncomputable section
variable {d : ℕ}

@[simp] theorem action_one (x : E d) : action (1 : OrthogonalGroup d) x = x := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin d) (Fin d) ℝ) x = x
  rw [map_one]
  rfl

@[simp] theorem action_inverse_cancel (B : OrthogonalGroup d) (x : E d) :
    action B (action B⁻¹ x) = x := by
  rw [← action_mul, mul_inv_cancel, action_one]

@[simp] theorem action_inverse_cancel_left (B : OrthogonalGroup d) (x : E d) :
    action B⁻¹ (action B x) = x := by
  rw [← action_mul, inv_mul_cancel, action_one]

theorem action_on_basis_entry (B : OrthogonalGroup d) (i j : Fin d) :
    action B ((EuclideanSpace.basisFun (Fin d) ℝ) j) i =
      (B : Matrix (Fin d) (Fin d) ℝ) i j := by
  change (∑ k : Fin d, (B : Matrix (Fin d) (Fin d) ℝ) i k *
    (EuclideanSpace.basisFun (Fin d) ℝ j) k) = _
  simp [EuclideanSpace.basisFun_apply]

def liftResidual (r : ℕ) (hr : r ≤ d) (y : E (d-r)) : E d :=
  WithLp.toLp 2 (fun i => if hi : i.val < r then 0 else y ⟨i.val-r,by omega⟩)

def prefixPart (r : ℕ) (x : E d) : E d :=
  WithLp.toLp 2 (fun i => if i.val < r then x i else 0)

theorem coordinate_decomposition (r : ℕ) (hr : r ≤ d) (x : E d) :
    x = prefixPart r x + liftResidual r hr (residualCoordinates r hr x) := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i.val < r
  · simp [prefixPart, liftResidual, hi]
  · have hindex := indexSplit_residual_eq d r hr i hi
    simp [prefixPart, liftResidual, residualCoordinates, hi, hindex]

theorem liftResidual_smul (r : ℕ) (hr : r ≤ d) (a : ℝ) (y : E (d-r)) :
    liftResidual r hr (a • y) = a • liftResidual r hr y := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i.val < r <;> simp [liftResidual, hi]

theorem normalizedResidual_rescale (r : ℕ) (hr : r ≤ d) (x : E d)
    (hx : residualCoordinates r hr x ≠ 0) :
    ‖residualCoordinates r hr x‖ • normalizedResidual r hr x = residualCoordinates r hr x := by
  simp [normalizedResidual, smul_smul, norm_ne_zero_iff.mpr hx]

/-- The new ambient pivot is exactly the lift of the normalized residual vector. -/
theorem fullResidualStep_maps_pivot_lift (r : Fin d) (x : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) x ≠ 0) :
    action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r) =
      liftResidual r.val (Nat.le_of_lt r.isLt)
        (normalizedResidual r.val (Nat.le_of_lt r.isLt) x) := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [action_on_basis_entry]
  rw [fullResidualStep, blockOrthogonal_apply]
  simp only [lt_self_iff_false, dite_false]
  by_cases hi : i.val < r.val
  · have hifin : i < r := hi
    simp [liftResidual, hi, hifin]
  · have hifin : ¬ i < r := hi
    rw [dif_neg hi]
    have hp := congrArg (fun v : E (d-r.val) => v ⟨i.val-r.val,by omega⟩)
      (residualHouseholder_maps_pivot r x hx)
    rw [action_on_basis_entry] at hp
    simpa [liftResidual, hi, hifin, residualPivot] using hp

/-- Exact query decomposition used to prove that new residual rotations fix the reply. -/
theorem query_decomposition (r : Fin d) (x : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) x ≠ 0) :
    x = prefixPart r.val x + ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) x‖ •
      action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r) := by
  rw [fullResidualStep_maps_pivot_lift r x hx, ← liftResidual_smul,
    normalizedResidual_rescale r.val (Nat.le_of_lt r.isLt) x hx]
  exact coordinate_decomposition r.val (Nat.le_of_lt r.isLt) x

/-- The old measured component has an explicit canonical-basis expansion. -/
theorem prefixPart_eq_sum (r : ℕ) (x : E d) :
    prefixPart r x = ∑ j : Fin d, if j.val < r then
      x j • ((EuclideanSpace.basisFun (Fin d) ℝ) j) else 0 := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (prefixPart r x)
  simpa [prefixPart, ite_smul] using h.symm

theorem action_fixes_prefixPart (r : ℕ) (B : OrthogonalGroup d)
    (hfix : ∀ j : Fin d, j.val < r →
      action B ((EuclideanSpace.basisFun (Fin d) ℝ) j) =
        (EuclideanSpace.basisFun (Fin d) ℝ) j) (x : E d) :
    action B (prefixPart r x) = prefixPart r x := by
  rw [prefixPart_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j.val < r
  · simp only [if_pos hji, map_smul, hfix j hji]
  · simp only [if_neg hji, map_zero]

#print axioms coordinate_decomposition
#print axioms fullResidualStep_maps_pivot_lift
#print axioms query_decomposition
#print axioms prefixPart_eq_sum
#print axioms action_fixes_prefixPart
end
end Task006.AdaptiveSphereGeometry
