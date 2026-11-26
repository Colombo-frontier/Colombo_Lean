import LowRank.ProjectorExtension

/-! A measurable projector containing all columns of an arbitrary matrix,
with rank at most its number of columns. Linear dependencies and zero
columns are covered by the same total recursive construction. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def columnRangeProjector {d : ℕ} : {k : ℕ} → Matrix (Fin d) (Fin k) ℝ →
    Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 0
  | k + 1, Z => extendProjector (columnRangeProjector (Z.submatrix id Fin.castSucc))
      (fun i => Z i (Fin.last k))

theorem columnRangeProjector_isProjector {d k : ℕ} (Z : Matrix (Fin d) (Fin k) ℝ) :
    IsOrthogonalProjector (columnRangeProjector Z) := by
  induction k with
  | zero => exact ⟨by simp [columnRangeProjector], by simp [columnRangeProjector]⟩
  | succ k ih => exact extendProjector_isProjector (ih _) _

theorem columnRangeProjector_fixes {d k : ℕ} (Z : Matrix (Fin d) (Fin k) ℝ) :
    columnRangeProjector Z * Z = Z := by
  induction k with
  | zero => ext i j; exact Fin.elim0 j
  | succ k ih =>
    let W := Z.submatrix id Fin.castSucc
    have hW := ih W
    ext i j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · exact congrFun (extendProjector_fixes_new (columnRangeProjector_isProjector W)
        (fun a => Z a (Fin.last k))) i
    · have hcol : columnRangeProjector W *ᵥ (fun a => Z a l.castSucc) =
          (fun a => Z a l.castSucc) := by
        funext a
        exact congrFun (congrFun hW a) l
      exact congrFun (extendProjector_fixes_original (columnRangeProjector_isProjector W)
        (fun a => Z a (Fin.last k)) (fun a => Z a l.castSucc) hcol) i

theorem columnRangeProjector_trace_le {d k : ℕ} (Z : Matrix (Fin d) (Fin k) ℝ) :
    (columnRangeProjector Z).trace ≤ k := by
  induction k with
  | zero => simp [columnRangeProjector]
  | succ k ih =>
    change (extendProjector _ _).trace ≤ (k + 1 : ℕ)
    calc
      _ ≤ (columnRangeProjector (Z.submatrix id Fin.castSucc)).trace + 1 :=
        extendProjector_trace_le _ _
      _ ≤ (k : ℝ) + 1 := add_le_add_right (ih _) 1
      _ = (k + 1 : ℕ) := by norm_cast

theorem columnRangeProjector_rank_le {d k : ℕ} (Z : Matrix (Fin d) (Fin k) ℝ) :
    (columnRangeProjector Z).rank ≤ k := by
  have h := columnRangeProjector_trace_le Z
  rw [(columnRangeProjector_isProjector Z).trace_eq_rank] at h
  exact_mod_cast h

theorem measurable_columnRangeProjector (d k : ℕ) :
    Measurable (columnRangeProjector : Matrix (Fin d) (Fin k) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hW : Measurable (fun Z : Matrix (Fin d) (Fin (k + 1)) ℝ =>
        Z.submatrix id Fin.castSucc) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      exact (measurable_pi_apply j.castSucc).comp (measurable_pi_apply i)
    have hz : Measurable (fun Z : Matrix (Fin d) (Fin (k + 1)) ℝ =>
        fun i => Z i (Fin.last k)) := by
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply (Fin.last k)).comp (measurable_pi_apply i)
    exact (measurable_extendProjector d).comp ((ih.comp hW).prodMk hz)

end
end LowRank
