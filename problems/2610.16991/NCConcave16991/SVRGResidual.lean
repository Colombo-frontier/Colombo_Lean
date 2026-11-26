import NCConcave16991.VariationalInequality
import Mathlib.Tactic.Abel

/-!
# Computable residual after a full projected forward step

The normal vector is constructed explicitly from the projection.  Its membership
in the outward normal cone and the residual estimate are proved from the actual
projection and the VI, rather than assumed as a certificate.
-/

noncomputable section

open Set
open scoped InnerProductSpace

namespace NCConcave16991.SVRG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- The outward normal cone, with its defining supporting-halfspace convention. -/
def normalCone (z : E) : Set E := {v | ∀ w ∈ S, ⟪v, w - z⟫_ℝ ≤ 0}

/-- One full operator evaluation followed by the actual feasible projection. -/
def fullStep (T : E → E) (ell : ℝ) (z : S) : S :=
  VariationalInequality.projectedStep S hne hclosed hconvex T ell⁻¹ z

/-- The explicitly computed normal vector at the projected point. -/
def fullStepNormal (T : E → E) (ell : ℝ) (z : S) : E :=
  ell • ((z : E) - fullStep S hne hclosed hconvex T ell z) - T z

/-- A second full evaluation gives an actual normal-cone residual. -/
def fullStepResidual (T : E → E) (ell : ℝ) (z : S) : E :=
  T (fullStep S hne hclosed hconvex T ell z) +
    fullStepNormal S hne hclosed hconvex T ell z

theorem fullStepNormal_mem (T : E → E) {ell : ℝ} (hell : 0 < ell) (z : S) :
    fullStepNormal S hne hclosed hconvex T ell z ∈
      normalCone S (fullStep S hne hclosed hconvex T ell z) := by
  intro w hw
  have hp := VariationalInequality.projection_inner S hne hclosed hconvex
    ((z : E) - ell⁻¹ • T z) w hw
  change ⟪(z : E) - ell⁻¹ • T z -
    (fullStep S hne hclosed hconvex T ell z : E),
      w - (fullStep S hne hclosed hconvex T ell z : E)⟫_ℝ ≤ 0 at hp
  have hid : fullStepNormal S hne hclosed hconvex T ell z =
      ell • ((z : E) - ell⁻¹ • T z -
        (fullStep S hne hclosed hconvex T ell z : E)) := by
    simp only [fullStepNormal, smul_sub, smul_smul, mul_inv_cancel₀ hell.ne', one_smul]
    abel
  rw [hid, real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos hell.le hp

theorem fullStep_fixed (T : E → E) {ell : ℝ} (hell : 0 < ell) (star : S)
    (hstar : VariationalInequality.IsSolution S T star) :
    fullStep S hne hclosed hconvex T ell star = star :=
  (VariationalInequality.projectedStep_fixed_iff S hne hclosed hconvex T
    (inv_pos.mpr hell) star).2 hstar

/-- The projected full step is 2-Lipschitz under ell-Lipschitz continuity of T. -/
theorem fullStep_lipschitz (T : E → E) {ell : ℝ} (hell : 0 < ell)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ≤ ell * ‖x - y‖) (x y : S) :
    ‖(fullStep S hne hclosed hconvex T ell x : E) -
      fullStep S hne hclosed hconvex T ell y‖ ≤ 2 * ‖(x : E) - y‖ := by
  have hp := VariationalInequality.projection_nonexpansive S hne hclosed hconvex
    ((x : E) - ell⁻¹ • T x) ((y : E) - ell⁻¹ • T y)
  change ‖(fullStep S hne hclosed hconvex T ell x : E) -
    fullStep S hne hclosed hconvex T ell y‖ ≤ _ at hp
  have hdiff : ((x : E) - ell⁻¹ • T x) - ((y : E) - ell⁻¹ • T y) =
      ((x : E) - y) - ell⁻¹ • (T x - T y) := by rw [smul_sub]; abel
  rw [hdiff] at hp
  have ht := norm_sub_le ((x : E) - y) (ell⁻¹ • (T x - T y))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hell)] at ht
  have hb := mul_le_mul_of_nonneg_left (hLip x x.property y y.property)
    (inv_nonneg.mpr hell.le)
  have heq : ell⁻¹ * (ell * ‖(x : E) - y‖) = ‖(x : E) - y‖ := by
    rw [← mul_assoc, inv_mul_cancel₀ hell.ne', one_mul]
  rw [heq] at hb
  linarith

theorem fullStep_distance_to_solution (T : E → E) {ell : ℝ} (hell : 0 < ell)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ≤ ell * ‖x - y‖)
    (z star : S) (hstar : VariationalInequality.IsSolution S T star) :
    ‖(fullStep S hne hclosed hconvex T ell z : E) - star‖ ≤ 2 * ‖(z : E) - star‖ := by
  simpa only [fullStep_fixed S hne hclosed hconvex T hell star hstar] using
    fullStep_lipschitz S hne hclosed hconvex T hell hLip z star

theorem fullStep_displacement (T : E → E) {ell : ℝ} (hell : 0 < ell)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ≤ ell * ‖x - y‖)
    (z star : S) (hstar : VariationalInequality.IsSolution S T star) :
    ‖(z : E) - fullStep S hne hclosed hconvex T ell z‖ ≤ 3 * ‖(z : E) - star‖ := by
  have ht := norm_sub_le ((z : E) - star)
    ((fullStep S hne hclosed hconvex T ell z : E) - star)
  have hid : ((z : E) - star) -
      ((fullStep S hne hclosed hconvex T ell z : E) - star) =
      (z : E) - fullStep S hne hclosed hconvex T ell z := by abel
  rw [hid] at ht
  have hp := fullStep_distance_to_solution S hne hclosed hconvex T hell hLip z star hstar
  linarith

/-- The observable residual is at most 6 ell times the distance to the unknown VI solution. -/
theorem fullStepResidual_bound (T : E → E) {ell : ℝ} (hell : 0 < ell)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ≤ ell * ‖x - y‖)
    (z star : S) (hstar : VariationalInequality.IsSolution S T star) :
    ‖fullStepResidual S hne hclosed hconvex T ell z‖ ≤ 6 * ell * ‖(z : E) - star‖ := by
  let p : S := fullStep S hne hclosed hconvex T ell z
  have hid : fullStepResidual S hne hclosed hconvex T ell z =
      (T p - T z) + ell • ((z : E) - p) := by
    dsimp [fullStepResidual, fullStepNormal, p]
    abel
  rw [hid]
  have ht := norm_add_le (T p - T z) (ell • ((z : E) - p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hell] at ht
  have hl := hLip p p.property z z.property
  rw [norm_sub_rev (p : E) (z : E)] at hl
  have hd := fullStep_displacement S hne hclosed hconvex T hell hLip z star hstar
  change ‖(z : E) - p‖ ≤ _ at hd
  nlinarith

theorem fullStepResidual_sq_bound (T : E → E) {ell : ℝ} (hell : 0 < ell)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ≤ ell * ‖x - y‖)
    (z star : S) (hstar : VariationalInequality.IsSolution S T star) :
    ‖fullStepResidual S hne hclosed hconvex T ell z‖ ^ 2 ≤
      36 * ell ^ 2 * ‖(z : E) - star‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (fullStepResidual_bound S hne hclosed hconvex T hell hLip z star hstar) 2
  nlinarith

end NCConcave16991.SVRG
