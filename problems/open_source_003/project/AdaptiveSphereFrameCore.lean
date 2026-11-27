import HaarRebalancingAction
import AdaptiveSphereHaar

/-!
Explicit measurable Householder rotations for the adaptive measurement frame.
The rational formula uses totalized real division, so zero normals produce the
identity and no nonconstructive measurable frame choice is needed.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace Matrix

set_option maxHeartbeats 1000000

namespace Task006.AdaptiveSphereFrame

open Task006.HaarRebalancing

noncomputable section

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- Reflection in the hyperplane normal to w, including w=0. -/
def householder (w : E d) : E d ≃ₗᵢ[ℝ] E d := (ℝ ∙ w).orthogonal.reflection

theorem householder_apply (w x : E d) :
    householder w x = x - (2 * inner ℝ w x / ‖w‖ ^ 2) • w := by
  rw [householder, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [neg_sub]
  module

/-- Joint Borel measurability of the actual rotation action. -/
theorem measurable_householder_apply :
    Measurable (fun p : E d × E d => householder p.1 p.2) := by
  simp only [householder_apply]
  exact measurable_snd.sub
    ((((measurable_fst.inner measurable_snd).const_mul 2).div
      (measurable_fst.norm.pow_const 2)).smul measurable_fst)

def householderMatrix (w : E d) : OrthogonalGroup d :=
  orthogonalMatrixOfLinearIsometryEquiv (householder w)

/-- Matrix entries are obtained by applying the reflection to canonical vectors. -/
theorem householderMatrix_entry (w : E d) (i j : Fin d) :
    (householderMatrix w : Matrix (Fin d) (Fin d) ℝ) i j =
      (householder w ((EuclideanSpace.basisFun (Fin d) ℝ) j)) i := by
  change (LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (householder w).toLinearMap) i j = _
  rw [LinearMap.toMatrix_apply]
  simp

/-- Coordinatewise measurability implies measurability for the chosen Borel
matrix structure, without silently switching matrix measurable instances. -/
theorem measurable_matrix_of_entries {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ i j, Measurable (fun ω => F ω i j)) : Measurable F := by
  have hpi : @Measurable Ω (Fin d → Fin d → ℝ) inferInstance MeasurableSpace.pi F := by
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hF i j
  have heq : (MeasurableSpace.pi : MeasurableSpace (Fin d → Fin d → ℝ)) =
      realMatrixMeasurableSpace d :=
    @BorelSpace.measurable_eq (Fin d → Fin d → ℝ) inferInstance MeasurableSpace.pi inferInstance
  change @Measurable Ω (Matrix (Fin d) (Fin d) ℝ) inferInstance (realMatrixMeasurableSpace d) F
  rw [← heq]
  exact hpi

theorem householderMatrix_entry_formula (w : E d) (i j : Fin d) :
    (householderMatrix w : Matrix (Fin d) (Fin d) ℝ) i j =
      (if i = j then 1 else 0) - (2 * w j / ‖w‖ ^ 2) * w i := by
  rw [householderMatrix_entry, householder_apply, EuclideanSpace.inner_basisFun_real]
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem measurable_householderMatrix_coe : Measurable
    (fun w : E d => (householderMatrix w : Matrix (Fin d) (Fin d) ℝ)) := by
  apply measurable_matrix_of_entries
  intro i j
  have hi : Measurable (fun w : E d => w i) := (EuclideanSpace.proj i).continuous.measurable
  have hj : Measurable (fun w : E d => w j) := (EuclideanSpace.proj j).continuous.measurable
  have hn : Measurable (fun w : E d => ‖w‖ ^ 2) := measurable_id.norm.pow_const 2
  have hf : Measurable (fun w : E d =>
      (if i = j then 1 else 0) - (2 * w j / ‖w‖ ^ 2) * w i) :=
    measurable_const.sub (((hj.const_mul 2).div hn).mul hi)
  have heq : (fun w : E d => (householderMatrix w : Matrix (Fin d) (Fin d) ℝ) i j) =
      (fun w : E d => (if i = j then 1 else 0) - (2 * w j / ‖w‖ ^ 2) * w i) := by
    funext w
    exact householderMatrix_entry_formula w i j
  rw [heq]
  exact hf


/-- The orthogonal-group-valued map has exactly the induced Borel structure. -/
theorem measurable_householderMatrix : Measurable (householderMatrix (d := d)) :=
  measurable_comap_iff.mpr (measurable_householderMatrix_coe (d := d))

theorem action_householderMatrix (w x : E d) :
    action (householderMatrix w) x = householder w x :=
  action_matrixOfIsometry _ _

/-- Equal-radius vectors are mapped exactly, including the coincident case. -/
theorem householder_maps_equal_norm (x y : E d) (hxy : ‖x‖ = ‖y‖) :
    action (householderMatrix (x - y)) x = y := by
  rw [action_householderMatrix]
  exact Submodule.reflection_sub hxy

/-- Every previously measured direction orthogonal to the normal stays fixed. -/
theorem householder_fixes_orthogonal (w x : E d) (hwx : inner ℝ w x = 0) :
    action (householderMatrix w) x = x := by
  rw [action_householderMatrix]
  apply Submodule.reflection_mem_subspace_eq_self
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hwx

/-- Coordinates not yet measured, in the current orthogonal frame. -/
def tailCoordinates (r : ℕ) (x : E d) : E d :=
  WithLp.toLp 2 (fun i => if i.val < r then 0 else x i)

theorem continuous_tailCoordinates (r : ℕ) : Continuous (tailCoordinates (d := d) r) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i.val < r
  · simpa [tailCoordinates, hi] using (continuous_const : Continuous (fun _ : E d => (0 : ℝ)))
  · simpa [tailCoordinates, hi] using (EuclideanSpace.proj i).continuous

@[simp] theorem tailCoordinates_prefix (r : ℕ) (x : E d) (i : Fin d) (hi : i.val < r) :
    tailCoordinates r x i = 0 := by simp [tailCoordinates, hi]

@[simp] theorem tailCoordinates_tail (r : ℕ) (x : E d) (i : Fin d) (hi : r ≤ i.val) :
    tailCoordinates r x i = x i := by simp [tailCoordinates, not_lt.mpr hi]

def normalizedTail (r : ℕ) (x : E d) : E d :=
  ‖tailCoordinates r x‖⁻¹ • tailCoordinates r x

theorem measurable_normalizedTail (r : ℕ) : Measurable (normalizedTail (d := d) r) := by
  exact ((continuous_tailCoordinates r).measurable.norm.inv).smul
    (continuous_tailCoordinates r).measurable

theorem normalizedTail_norm (r : ℕ) (x : E d) (hx : tailCoordinates r x ≠ 0) :
    ‖normalizedTail r x‖ = 1 := by
  simp [normalizedTail, norm_smul, norm_ne_zero_iff.mpr hx]

/-- A measurable orthogonal frame update for a chosen pivot position. -/
def frameStep (r : Fin d) (x : E d) : OrthogonalGroup d :=
  if tailCoordinates r.val x = 0 then 1 else
    householderMatrix ((EuclideanSpace.basisFun (Fin d) ℝ) r - normalizedTail r.val x)

theorem measurable_frameStep (r : Fin d) : Measurable (frameStep r) := by
  apply Measurable.ite
    ((continuous_tailCoordinates r.val).measurable (measurableSet_singleton 0))
    measurable_const
  exact measurable_householderMatrix.comp
    (measurable_const.sub (measurable_normalizedTail r.val))

/-- When a new independent direction exists, the new pivot points exactly along it. -/
theorem frameStep_maps_pivot (r : Fin d) (x : E d)
    (hx : tailCoordinates r.val x ≠ 0) :
    action (frameStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) r) =
      normalizedTail r.val x := by
  rw [frameStep, if_neg hx]
  apply householder_maps_equal_norm
  rw [(EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one r,
    normalizedTail_norm r.val x hx]

@[simp] theorem normalizedTail_prefix (r : ℕ) (x : E d) (j : Fin d) (hj : j.val < r) :
    normalizedTail r x j = 0 := by
  simp [normalizedTail, tailCoordinates, hj]

/-- Earlier canonical basis vectors are fixed by the explicit frame step. -/
theorem frameStep_fixes_prefix (r : Fin d) (x : E d) (j : Fin d) (hj : j.val < r.val) :
    action (frameStep r x) ((EuclideanSpace.basisFun (Fin d) ℝ) j) =
      (EuclideanSpace.basisFun (Fin d) ℝ) j := by
  by_cases hx : tailCoordinates r.val x = 0
  · rw [frameStep, if_pos hx]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin d) (Fin d) ℝ)
      ((EuclideanSpace.basisFun (Fin d) ℝ) j) = _
    rw [map_one]
    rfl
  · rw [frameStep, if_neg hx]
    apply householder_fixes_orthogonal
    rw [inner_sub_left, EuclideanSpace.inner_basisFun_real,
      EuclideanSpace.inner_basisFun_real, normalizedTail_prefix r.val x j hj]
    have hrj : r ≠ j := by
      intro h
      subst j
      omega
    simp [EuclideanSpace.basisFun_apply, hrj]

#print axioms measurable_householderMatrix
#print axioms measurable_frameStep
#print axioms frameStep_maps_pivot
#print axioms frameStep_fixes_prefix
end
end Task006.AdaptiveSphereFrame
