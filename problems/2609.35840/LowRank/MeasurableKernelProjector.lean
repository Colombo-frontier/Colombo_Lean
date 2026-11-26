import LowRank.ColumnRangeProjector

/-! The recursive column projector has exactly the generated column space.
Its complement on the transpose gives a total measurable kernel projector,
including rank changes and singular matrices. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem columnRangeProjector_left_annihilator {a d k : ℕ}
    (A : Matrix (Fin a) (Fin d) ℝ) (Z : Matrix (Fin d) (Fin k) ℝ)
    (hAZ : A * Z = 0) : A * columnRangeProjector Z = 0 := by
  induction k with
  | zero => simp [columnRangeProjector]
  | succ k ih =>
      let W := Z.submatrix id Fin.castSucc
      let z := fun i => Z i (Fin.last k)
      have hAW : A * W = 0 := by
        ext i j
        exact congrFun (congrFun hAZ i) j.castSucc
      have hAz : A *ᵥ z = 0 := by
        ext i
        exact congrFun (congrFun hAZ i) (Fin.last k)
      have hAP := ih W hAW
      have hres : A *ᵥ ((1 - columnRangeProjector W) *ᵥ z) = 0 := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec, hAP, Matrix.zero_mulVec, sub_zero, hAz]
      change A * (columnRangeProjector W + rankOneProjector ((1 - columnRangeProjector W) *ᵥ z)) = 0
      rw [Matrix.mul_add, hAP, mul_rankOneProjector_eq_zero A _ hres, add_zero]

theorem columnRangeProjector_right_annihilator {d k t : ℕ}
    (Z : Matrix (Fin d) (Fin k) ℝ) (B : Matrix (Fin d) (Fin t) ℝ)
    (h : Zᵀ * B = 0) : columnRangeProjector Z * B = 0 := by
  have ht := congrArg Matrix.transpose h
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at ht
  have hp := congrArg Matrix.transpose (columnRangeProjector_left_annihilator Bᵀ Z ht)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    (columnRangeProjector_isProjector Z).symmetric] using hp

theorem columnRangeProjector_kills_kernel {d k : ℕ}
    (Z : Matrix (Fin d) (Fin k) ℝ) (v : Fin d → ℝ) (h : Zᵀ *ᵥ v = 0) :
    columnRangeProjector Z *ᵥ v = 0 := by
  let B : Matrix (Fin d) (Fin 1) ℝ := fun i _ => v i
  have hB : Zᵀ * B = 0 := by
    ext i j
    exact congrFun h i
  have hp := columnRangeProjector_right_annihilator Z B hB
  ext i
  exact congrFun (congrFun hp i) 0

def measurableKernelProjector {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := 1 - columnRangeProjector Aᵀ

theorem measurableKernelProjector_isProjector {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ) :
    IsOrthogonalProjector (measurableKernelProjector A) :=
  (columnRangeProjector_isProjector Aᵀ).complement

theorem mul_measurableKernelProjector {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ) :
    A * measurableKernelProjector A = 0 := by
  have h := congrArg Matrix.transpose (columnRangeProjector_fixes Aᵀ)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    (columnRangeProjector_isProjector Aᵀ).symmetric] at h
  rw [measurableKernelProjector, Matrix.mul_sub, Matrix.mul_one, h, sub_self]

theorem measurableKernelProjector_fixes {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (v : Fin d → ℝ) (h : A *ᵥ v = 0) : measurableKernelProjector A *ᵥ v = v := by
  have hp := columnRangeProjector_kills_kernel Aᵀ v (by simpa only [Matrix.transpose_transpose] using h)
  rw [measurableKernelProjector, Matrix.sub_mulVec, Matrix.one_mulVec, hp, sub_zero]

theorem measurableKernelProjector_ne_zero {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (h : ∃ v : Fin d → ℝ, v ≠ 0 ∧ A *ᵥ v = 0) : measurableKernelProjector A ≠ 0 := by
  obtain ⟨v, hv, hAv⟩ := h
  intro hz
  have hfix := measurableKernelProjector_fixes A v hAv
  rw [hz, Matrix.zero_mulVec] at hfix
  exact hv hfix.symm

theorem measurable_measurableKernelProjector (a d : ℕ) :
    Measurable (measurableKernelProjector : Matrix (Fin a) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  have htrans : Measurable (Matrix.transpose : Matrix (Fin a) (Fin d) ℝ → _) := by fun_prop
  have hP := (measurable_columnRangeProjector d a).comp htrans
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_const.sub ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hP))

end
end LowRank
