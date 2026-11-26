import LowRank.ProjectorExtension

/-! A measurable one-vector extension which stops once the target rank
has been reached. Rank integrality ensures that the cap cannot be exceeded. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def cappedProjectorExtension {d : ℕ} (k : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if P.trace < (k : ℝ) then extendProjector P z else P

theorem cappedProjectorExtension_isProjector {d k : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) :
    IsOrthogonalProjector (cappedProjectorExtension k P z) := by
  unfold cappedProjectorExtension
  split_ifs
  · exact extendProjector_isProjector hP z
  · exact hP

theorem cappedProjectorExtension_trace_ge {d k : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) :
    P.trace ≤ (cappedProjectorExtension k P z).trace := by
  unfold cappedProjectorExtension
  split_ifs
  · rw [extendProjector, Matrix.trace_add]
    exact le_add_of_nonneg_right (psd_trace_nonneg (rankOneProjector_isProjector _).posSemidef)
  · exact le_rfl

theorem cappedProjectorExtension_rank_le {d k : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank ≤ k) (z : Fin d → ℝ) :
    (cappedProjectorExtension k P z).rank ≤ k := by
  unfold cappedProjectorExtension
  split_ifs with ht
  · have hr : P.rank < k := by rw [hP.trace_eq_rank] at ht; exact_mod_cast ht
    have htr : (extendProjector P z).trace ≤ (k : ℝ) := by
      calc
        _ ≤ P.trace + 1 := extendProjector_trace_le P z
        _ = (P.rank + 1 : ℕ) := by rw [hP.trace_eq_rank]; norm_cast
        _ ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hr
    rw [(extendProjector_isProjector hP z).trace_eq_rank] at htr
    exact_mod_cast htr
  · exact hrank

theorem cappedProjectorExtension_mul_original {d k : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) :
    cappedProjectorExtension k P z * P = P := by
  unfold cappedProjectorExtension
  split_ifs
  · exact extendProjector_mul_original hP z
  · exact hP.idempotent

theorem cappedProjectorExtension_fixes_original {d k : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z v : Fin d → ℝ) (hv : P *ᵥ v = v) :
    cappedProjectorExtension k P z *ᵥ v = v := by
  calc
    _ = cappedProjectorExtension k P z *ᵥ (P *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, cappedProjectorExtension_mul_original hP z, hv]

theorem cappedProjectorExtension_fixes_new {d k : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (ht : P.trace < (k : ℝ)) (z : Fin d → ℝ) :
    cappedProjectorExtension k P z *ᵥ z = z := by
  rw [cappedProjectorExtension, if_pos ht]
  exact extendProjector_fixes_new hP z

theorem measurable_cappedProjectorExtension (d k : ℕ) : Measurable
    (fun x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => cappedProjectorExtension k x.1 x.2) := by
  have ht : Continuous (fun x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => x.1.trace) := by
    fun_prop
  exact Measurable.ite (measurableSet_lt ht.measurable measurable_const)
    (measurable_extendProjector d) measurable_fst

end
end LowRank
