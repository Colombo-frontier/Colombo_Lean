import LowRank.ColumnRangeProjector

/-! Recover A times the column-space projector from a pair (K, A K),
without any further access to A. The total measurable construction handles
zero and dependent columns by the same Gram-Schmidt recursion. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def columnRangeImage {a d : ℕ} : {k : ℕ} →
    Matrix (Fin d) (Fin k) ℝ → Matrix (Fin a) (Fin k) ℝ → Matrix (Fin a) (Fin d) ℝ
  | 0, _, _ => 0
  | k + 1, K, Y =>
      let W := K.submatrix id Fin.castSucc
      let z := fun i => K i (Fin.last k)
      let V := columnRangeImage W (Y.submatrix id Fin.castSucc)
      let u := (1 - columnRangeProjector W) *ᵥ z
      V + (u ⬝ᵥ u)⁻¹ • vecMulVec ((fun i => Y i (Fin.last k)) - V *ᵥ z) u

theorem columnRangeImage_mul {a d k : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin k) ℝ) :
    columnRangeImage K (A * K) = A * columnRangeProjector K := by
  induction k with
  | zero => simp [columnRangeImage, columnRangeProjector]
  | succ k ih =>
      let W := K.submatrix id Fin.castSucc
      let z := fun i => K i (Fin.last k)
      have hprefix : (A * K).submatrix id Fin.castSucc = A * W := rfl
      have hcol : (fun i => (A * K) i (Fin.last k)) = A *ᵥ z := rfl
      change columnRangeImage W ((A * K).submatrix id Fin.castSucc) +
        (((1 - columnRangeProjector W) *ᵥ z) ⬝ᵥ ((1 - columnRangeProjector W) *ᵥ z))⁻¹ •
          vecMulVec ((fun i => (A * K) i (Fin.last k)) -
            columnRangeImage W ((A * K).submatrix id Fin.castSucc) *ᵥ z)
            ((1 - columnRangeProjector W) *ᵥ z) =
        A * (columnRangeProjector W + rankOneProjector ((1 - columnRangeProjector W) *ᵥ z))
      rw [hprefix, ih, hcol, Matrix.mul_add, rankOneProjector, Matrix.mul_smul, mul_outer]
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]

theorem measurable_columnRangeImage (a d k : ℕ) :
    Measurable (fun x : Matrix (Fin d) (Fin k) ℝ × Matrix (Fin a) (Fin k) ℝ =>
      columnRangeImage x.1 x.2) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      let D := Matrix (Fin d) (Fin (k + 1)) ℝ × Matrix (Fin a) (Fin (k + 1)) ℝ
      have hW : Measurable (fun x : D => x.1.submatrix id Fin.castSucc) := by dsimp only [D]; fun_prop
      have hY : Measurable (fun x : D => x.2.submatrix id Fin.castSucc) := by dsimp only [D]; fun_prop
      have hz : Measurable (fun x : D => fun i => x.1 i (Fin.last k)) := by dsimp only [D]; fun_prop
      have hy : Measurable (fun x : D => fun i => x.2 i (Fin.last k)) := by dsimp only [D]; fun_prop
      have hV := ih.comp (hW.prodMk hY)
      have hP := (measurable_columnRangeProjector d k).comp hW
      have hres : Measurable (fun x : D =>
          (1 - columnRangeProjector (x.1.submatrix id Fin.castSucc)) *ᵥ
            (fun i => x.1 i (Fin.last k))) :=
        (show Continuous (fun t : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) =>
          (1 - t.1) *ᵥ t.2) by fun_prop).measurable.comp (hP.prodMk hz)
      have himage : Measurable (fun x : D =>
          (fun i => x.2 i (Fin.last k)) -
            columnRangeImage (x.1.submatrix id Fin.castSucc) (x.2.submatrix id Fin.castSucc) *ᵥ
              (fun i => x.1 i (Fin.last k))) :=
        hy.sub ((show Continuous (fun t : Matrix (Fin a) (Fin d) ℝ × (Fin d → ℝ) =>
          t.1 *ᵥ t.2) by fun_prop).measurable.comp (hV.prodMk hz))
      have hdot := (show Continuous (fun z : Fin d → ℝ => z ⬝ᵥ z) by fun_prop).measurable.comp hres
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      change Measurable (fun x : D =>
        columnRangeImage (x.1.submatrix id Fin.castSucc) (x.2.submatrix id Fin.castSucc) i j +
          _)
      exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hV)).add
        (hdot.inv.mul (((measurable_pi_apply i).comp himage).mul ((measurable_pi_apply j).comp hres)))

end
end LowRank
