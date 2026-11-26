import LowRank.MeasurableKernelProjector

/-! Concatenating two column spaces gives a measurable projector that
contains both. No full-rank or independence premise is needed. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def joinMatrixColumns {d s t : ℕ} (X : Matrix (Fin d) (Fin s) ℝ)
    (Y : Matrix (Fin d) (Fin t) ℝ) : Matrix (Fin d) (Fin (s + t)) ℝ :=
  fun i j => Fin.addCases (X i) (Y i) j

theorem measurable_joinMatrixColumns (d s t : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin s) ℝ × Matrix (Fin d) (Fin t) ℝ =>
      joinMatrixColumns p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · simpa only [joinMatrixColumns, Fin.addCases_left] using
      (measurable_pi_apply q).comp ((measurable_pi_apply i).comp measurable_fst)
  · simpa only [joinMatrixColumns, Fin.addCases_right] using
      (measurable_pi_apply q).comp ((measurable_pi_apply i).comp measurable_snd)

theorem mul_joinMatrixColumns {a d s t : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin s) ℝ) (Y : Matrix (Fin d) (Fin t) ℝ) :
    A * joinMatrixColumns X Y = joinMatrixColumns (A * X) (A * Y) := by
  ext i j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j <;>
    simp only [joinMatrixColumns, Matrix.mul_apply, Fin.addCases_left, Fin.addCases_right]

theorem columnRangeProjector_absorbed_of_fixes {d s : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) (X : Matrix (Fin d) (Fin s) ℝ)
    (h : P * X = X) : P * columnRangeProjector X = columnRangeProjector X := by
  have hz : (1 - P) * X = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  have hp := columnRangeProjector_left_annihilator (1 - P) X hz
  rw [Matrix.sub_mul, Matrix.one_mul] at hp
  exact (sub_eq_zero.mp hp).symm

theorem joinedColumnProjector_fixes_left {d s t : ℕ}
    (X : Matrix (Fin d) (Fin s) ℝ) (Y : Matrix (Fin d) (Fin t) ℝ) :
    columnRangeProjector (joinMatrixColumns X Y) * X = X := by
  have h := columnRangeProjector_fixes (joinMatrixColumns X Y)
  ext i j
  have hc := congrFun (congrFun h i) (j.castAdd t)
  simpa only [Matrix.mul_apply, joinMatrixColumns, Fin.addCases_left] using hc

theorem joinedColumnProjector_fixes_right {d s t : ℕ}
    (X : Matrix (Fin d) (Fin s) ℝ) (Y : Matrix (Fin d) (Fin t) ℝ) :
    columnRangeProjector (joinMatrixColumns X Y) * Y = Y := by
  have h := columnRangeProjector_fixes (joinMatrixColumns X Y)
  ext i j
  have hc := congrFun (congrFun h i) (j.natAdd s)
  simpa only [Matrix.mul_apply, joinMatrixColumns, Fin.addCases_right] using hc

theorem joinedColumnProjector_absorbs_left {d s t : ℕ}
    (X : Matrix (Fin d) (Fin s) ℝ) (Y : Matrix (Fin d) (Fin t) ℝ) :
    columnRangeProjector (joinMatrixColumns X Y) * columnRangeProjector X =
      columnRangeProjector X :=
  columnRangeProjector_absorbed_of_fixes _ X (joinedColumnProjector_fixes_left X Y)

theorem joinedColumnProjector_absorbs_right {d s t : ℕ}
    (X : Matrix (Fin d) (Fin s) ℝ) (Y : Matrix (Fin d) (Fin t) ℝ) :
    columnRangeProjector (joinMatrixColumns X Y) * columnRangeProjector Y =
      columnRangeProjector Y :=
  columnRangeProjector_absorbed_of_fixes _ Y (joinedColumnProjector_fixes_right X Y)

end
end LowRank
