import AdaptiveSphereGeometry
import AdaptiveSphereEmbedding

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereStabilizer

open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereGeometry

noncomputable section
variable {d : ℕ}

theorem block_fixes_basis (r : ℕ) (hr : r ≤ d) (g : OrthogonalGroup (d-r))
    (j : Fin d) (hj : j.val < r) :
    action (blockOrthogonal d r hr g) ((EuclideanSpace.basisFun (Fin d) ℝ) j) =
      (EuclideanSpace.basisFun (Fin d) ℝ) j := by
  simpa only [indexSplit_first_eq d r hr j hj] using
    blockOrthogonal_fixed_first d r hr g (⟨j.val,hj⟩ : Fin r)

theorem action_inv_fixes_of_fixes (B : OrthogonalGroup d) (v : E d)
    (hv : action B v = v) : action B⁻¹ v = v := by
  apply (action B).injective
  rw [action_inverse_cancel, hv]

def newFrameRotation (r : Fin d) (x : E d)
    (g : OrthogonalGroup (d-(r.val+1))) : OrthogonalGroup d :=
  fullResidualStep r x * blockOrthogonal d (r.val+1) (by omega) g *
    (fullResidualStep r x)⁻¹

theorem newFrameRotation_fixes_prefix (r : Fin d) (x : E d)
    (g : OrthogonalGroup (d-(r.val+1))) (j : Fin d) (hj : j.val < r.val) :
    action (newFrameRotation r x g) ((EuclideanSpace.basisFun (Fin d) ℝ) j) =
      (EuclideanSpace.basisFun (Fin d) ℝ) j := by
  have hH := fullResidualStep_fixes_prefix r x j hj
  have hHinv := action_inv_fixes_of_fixes (fullResidualStep r x)
    ((EuclideanSpace.basisFun (Fin d) ℝ) j) hH
  rw [newFrameRotation, action_mul, action_mul, hHinv,
    block_fixes_basis (r.val+1) (by omega) g j (by omega), hH]

theorem newFrameRotation_fixes_pivot (r : Fin d) (x : E d)
    (g : OrthogonalGroup (d-(r.val+1))) :
    action (newFrameRotation r x g)
        (action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r)) =
      action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r) := by
  rw [newFrameRotation, action_mul, action_mul, action_inverse_cancel_left,
    block_fixes_basis (r.val+1) (by omega) g r (Nat.lt_succ_self r.val)]

/-- A genuine next-rank stabilizer fixes the entire query, not just its new component. -/
theorem newFrameRotation_fixes_query (r : Fin d) (x : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) x ≠ 0)
    (g : OrthogonalGroup (d-(r.val+1))) :
    action (newFrameRotation r x g) x = x := by
  let R := newFrameRotation r x g
  have hprefix : action R (prefixPart r.val x) = prefixPart r.val x :=
    action_fixes_prefixPart r.val R (fun j hj => newFrameRotation_fixes_prefix r x g j hj) x
  have hdecomp := query_decomposition r x hx
  calc
    action R x = action R (prefixPart r.val x +
        ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) x‖ •
          action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r)) :=
      congrArg (action R) hdecomp
    _ = prefixPart r.val x + ‖residualCoordinates r.val (Nat.le_of_lt r.isLt) x‖ •
        action (fullResidualStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r) := by
      rw [map_add, map_smul, hprefix, newFrameRotation_fixes_pivot]
    _ = x := hdecomp.symm

/-- The old-history embedding produces exactly that query-fixing rotation. -/
theorem embedded_rotation_fixes_query (r : Fin d) (x : E d)
    (hx : residualCoordinates r.val (Nat.le_of_lt r.isLt) x ≠ 0)
    (g : OrthogonalGroup (d-(r.val+1))) :
    action (blockOrthogonal d r.val (Nat.le_of_lt r.isLt)
      (embedNext r (residualHouseholder r x) g)) x = x := by
  have heq : blockOrthogonal d r.val (Nat.le_of_lt r.isLt)
        (embedNext r (residualHouseholder r x) g) = newFrameRotation r x g := by
    simpa only [fullResidualStep, newFrameRotation] using
      embedNext_full_identity r (residualHouseholder r x) g
  rw [heq]
  exact newFrameRotation_fixes_query r x hx g

/-- If no rank is acquired, every old residual rotation already fixes the query. -/
theorem block_rotation_fixes_zero_residual (r : ℕ) (hr : r ≤ d) (x : E d)
    (hx : residualCoordinates r hr x = 0) (g : OrthogonalGroup (d-r)) :
    action (blockOrthogonal d r hr g) x = x := by
  have hlift : liftResidual r hr (0 : E (d-r)) = 0 := by
    apply WithLp.ofLp_injective 2
    funext i
    simp [liftResidual]
  have hdecomp := coordinate_decomposition r hr x
  rw [hx, hlift, add_zero] at hdecomp
  calc
    action (blockOrthogonal d r hr g) x =
        action (blockOrthogonal d r hr g) (prefixPart r x) :=
      congrArg (action (blockOrthogonal d r hr g)) hdecomp
    _ = prefixPart r x := action_fixes_prefixPart r _ (fun j hj => block_fixes_basis r hr g j hj) x
    _ = x := hdecomp.symm

theorem conjugated_action_fixes_query (B R : OrthogonalGroup d) (q : E d)
    (hfix : action R (action B⁻¹ q) = action B⁻¹ q) :
    action (B * R * B⁻¹) q = q := by
  rw [action_mul, action_mul, hfix, action_inverse_cancel]

#print axioms newFrameRotation_fixes_query
#print axioms embedded_rotation_fixes_query
#print axioms block_rotation_fixes_zero_residual
#print axioms conjugated_action_fixes_query
end
end Task006.AdaptiveSphereStabilizer
