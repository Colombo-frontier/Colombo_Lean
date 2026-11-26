import AdaptiveSphereFrameCore
import AdaptiveSphereBlock

/-! Explicit residual-coordinate Householder update and the stabilizer embedding
used by the actual adaptive symmetry induction. -/

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereResidualFrame

open Task006.HaarRebalancing Task006.AdaptiveSphereBlock Task006.AdaptiveSphereFrame

noncomputable section

variable {d : ℕ}

def residualCoordinates (r : ℕ) (hr : r ≤ d) (x : E d) : E (d - r) :=
  WithLp.toLp 2 (fun i => x (indexSplit d r hr (Sum.inr i)))

theorem continuous_residualCoordinates (r : ℕ) (hr : r ≤ d) :
    Continuous (residualCoordinates (d := d) r hr) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d-r) => ℝ)).comp
  apply continuous_pi
  intro i
  exact (EuclideanSpace.proj (indexSplit d r hr (Sum.inr i))).continuous

def normalizedResidual (r : ℕ) (hr : r ≤ d) (x : E d) : E (d-r) :=
  ‖residualCoordinates r hr x‖⁻¹ • residualCoordinates r hr x

theorem measurable_normalizedResidual (r : ℕ) (hr : r ≤ d) :
    Measurable (normalizedResidual (d := d) r hr) := by
  exact ((continuous_residualCoordinates r hr).measurable.norm.inv).smul
    (continuous_residualCoordinates r hr).measurable

theorem normalizedResidual_norm (r : ℕ) (hr : r ≤ d) (x : E d)
    (hx : residualCoordinates r hr x ≠ 0) : ‖normalizedResidual r hr x‖ = 1 := by
  simp [normalizedResidual, norm_smul, norm_ne_zero_iff.mpr hx]

def residualPivot (r : Fin d) : Fin (d-r.val) := ⟨0, by omega⟩

def residualHouseholder (r : Fin d) (x : E d) : OrthogonalGroup (d-r.val) :=
  if residualCoordinates r.val (Nat.le_of_lt r.isLt) x = 0 then 1 else
    householderMatrix
      ((EuclideanSpace.basisFun (Fin (d-r.val)) ℝ) (residualPivot r) -
        normalizedResidual r.val (Nat.le_of_lt r.isLt) x)

theorem measurable_residualHouseholder (r : Fin d) : Measurable (residualHouseholder r) := by
  apply Measurable.ite
    ((continuous_residualCoordinates r.val (Nat.le_of_lt r.isLt)).measurable
      (measurableSet_singleton 0)) measurable_const
  exact measurable_householderMatrix.comp
    (measurable_const.sub (measurable_normalizedResidual r.val (Nat.le_of_lt r.isLt)))

theorem residualHouseholder_maps_pivot (r : Fin d) (x : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) x ≠ 0) :
    action (residualHouseholder r x)
        ((EuclideanSpace.basisFun (Fin (d-r.val)) ℝ) (residualPivot r)) =
      normalizedResidual r.val (Nat.le_of_lt r.isLt) x := by
  rw [residualHouseholder, if_neg hx]
  apply householder_maps_equal_norm
  rw [(EuclideanSpace.basisFun (Fin (d-r.val)) ℝ).orthonormal.norm_eq_one (residualPivot r),
    normalizedResidual_norm r.val (Nat.le_of_lt r.isLt) x hx]

def fullResidualStep (r : Fin d) (x : E d) : OrthogonalGroup d :=
  blockOrthogonal d r.val (Nat.le_of_lt r.isLt) (residualHouseholder r x)

theorem measurable_fullResidualStep (r : Fin d) : Measurable (fullResidualStep r) :=
  (blockOrthogonal_measurable d r.val (Nat.le_of_lt r.isLt)).comp
    (measurable_residualHouseholder r)

theorem fullResidualStep_fixes_prefix (r : Fin d) (x : E d)
    (j : Fin d) (hj : j.val < r.val) :
    action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) j) =
      (EuclideanSpace.basisFun (Fin d) ℝ) j := by
  simpa only [fullResidualStep, indexSplit_first_eq d r.val (Nat.le_of_lt r.isLt) j hj] using
    blockOrthogonal_fixed_first d r.val (Nat.le_of_lt r.isLt) (residualHouseholder r x)
      (⟨j.val, hj⟩ : Fin r.val)

/-- The explicit block embedding as a group homomorphism. -/
def blockHom (d r : ℕ) (hr : r ≤ d) : OrthogonalGroup (d-r) →* OrthogonalGroup d where
  toFun := blockOrthogonal d r hr
  map_one' := blockOrthogonal_one d r hr
  map_mul' := blockOrthogonal_mul d r hr

theorem blockOrthogonal_inv (d r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d-r)) :
    blockOrthogonal d r hr g⁻¹ = (blockOrthogonal d r hr g)⁻¹ :=
  map_inv (blockHom d r hr) g

/-- A next-rank residual rotation, expressed entirely in the old residual space. -/
def embedNext (r : Fin d) (H : OrthogonalGroup (d-r.val))
    (g : OrthogonalGroup (d-(r.val+1))) : OrthogonalGroup (d-r.val) :=
  H * blockOrthogonal (d-r.val) 1 (by omega)
    (castOrthogonal (by omega) g) * H⁻¹

/-- The embedded rotation is exactly the conjugated new-frame rotation. -/
theorem embedNext_full_identity (r : Fin d) (H : OrthogonalGroup (d-r.val))
    (g : OrthogonalGroup (d-(r.val+1))) :
    blockOrthogonal d r.val (Nat.le_of_lt r.isLt) (embedNext r H g) =
      blockOrthogonal d r.val (Nat.le_of_lt r.isLt) H *
        blockOrthogonal d (r.val+1) (by omega) g *
          (blockOrthogonal d r.val (Nat.le_of_lt r.isLt) H)⁻¹ := by
  rw [embedNext, blockOrthogonal_mul, blockOrthogonal_mul, blockOrthogonal_inv,
    blockOrthogonal_nested d r.val (by omega) g]

#print axioms measurable_residualHouseholder
#print axioms residualHouseholder_maps_pivot
#print axioms measurable_fullResidualStep
#print axioms fullResidualStep_fixes_prefix
#print axioms embedNext_full_identity

end
end Task006.AdaptiveSphereResidualFrame
