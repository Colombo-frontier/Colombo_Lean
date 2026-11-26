import LowRank.MeasurableKernelProjector

/-! A total measurable choice of a unit vector from each nontrivial matrix
kernel, using the first nonzero column of its explicit kernel projector. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def firstNonzeroColumn {d : ℕ} : {k : ℕ} → Matrix (Fin d) (Fin k) ℝ → (Fin d → ℝ)
  | 0, _ => 0
  | k + 1, X => if (fun i => X i 0) = 0 then
      firstNonzeroColumn (X.submatrix id Fin.succ) else fun i => X i 0

theorem firstNonzeroColumn_ne_zero {d k : ℕ} (X : Matrix (Fin d) (Fin k) ℝ) (hX : X ≠ 0) :
    firstNonzeroColumn X ≠ 0 := by
  induction k with
  | zero => exact (hX (by ext i j; exact Fin.elim0 j)).elim
  | succ k ih =>
      simp only [firstNonzeroColumn]
      split_ifs with hcol
      · apply ih
        intro htail
        apply hX
        ext i j
        refine Fin.cases ?_ (fun l => ?_) j
        · exact congrFun hcol i
        · exact congrFun (congrFun htail i) l
      · exact hcol

theorem firstNonzeroColumn_annihilated {a d k : ℕ}
    (A : Matrix (Fin a) (Fin d) ℝ) (X : Matrix (Fin d) (Fin k) ℝ) (h : A * X = 0) :
    A *ᵥ firstNonzeroColumn X = 0 := by
  induction k with
  | zero => simp [firstNonzeroColumn]
  | succ k ih =>
      simp only [firstNonzeroColumn]
      split_ifs
      · apply ih
        ext i j
        exact congrFun (congrFun h i) j.succ
      · ext i
        exact congrFun (congrFun h i) 0

theorem measurable_firstNonzeroColumn (d k : ℕ) :
    Measurable (firstNonzeroColumn : Matrix (Fin d) (Fin k) ℝ → (Fin d → ℝ)) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have hcol : Measurable (fun X : Matrix (Fin d) (Fin (k + 1)) ℝ => fun i => X i 0) := by
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply 0).comp (measurable_pi_apply i)
      have htail : Measurable (fun X : Matrix (Fin d) (Fin (k + 1)) ℝ => X.submatrix id Fin.succ) := by
        apply measurable_pi_lambda
        intro i
        apply measurable_pi_lambda
        intro j
        exact (measurable_pi_apply j.succ).comp (measurable_pi_apply i)
      exact Measurable.ite ((measurableSet_singleton 0).preimage hcol) (ih.comp htail) hcol

def normalizeVector {d : ℕ} (v : Fin d → ℝ) : Fin d → ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v

theorem normalizeVector_dot_self {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    normalizeVector v ⬝ᵥ normalizeVector v = 1 := by
  have hnonneg : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne hnonneg
    (fun h => hv (_root_.dotProduct_self_eq_zero.mp h.symm))
  have hsqrt := Real.sq_sqrt hnonneg
  have hne : Real.sqrt (v ⬝ᵥ v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  simp only [normalizeVector, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← hsqrt]
  field_simp

theorem normalizeVector_annihilated {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (v : Fin d → ℝ) (h : A *ᵥ v = 0) : A *ᵥ normalizeVector v = 0 := by
  rw [normalizeVector, Matrix.mulVec_smul, h, smul_zero]

theorem measurable_normalizeVector (d : ℕ) : Measurable (normalizeVector (d := d)) := by
  have hdot : Measurable (fun v : Fin d → ℝ => v ⬝ᵥ v) := by
    simp only [dotProduct]
    fun_prop
  exact hdot.sqrt.inv.smul measurable_id

def kernelUnitVector {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ) : Fin d → ℝ :=
  normalizeVector (firstNonzeroColumn (measurableKernelProjector A))

theorem kernelUnitVector_in_kernel {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ) :
    A *ᵥ kernelUnitVector A = 0 :=
  normalizeVector_annihilated A _ (firstNonzeroColumn_annihilated A _ (mul_measurableKernelProjector A))

theorem kernelUnitVector_dot_self {a d : ℕ} (A : Matrix (Fin a) (Fin d) ℝ)
    (h : ∃ v : Fin d → ℝ, v ≠ 0 ∧ A *ᵥ v = 0) :
    kernelUnitVector A ⬝ᵥ kernelUnitVector A = 1 :=
  normalizeVector_dot_self _ (firstNonzeroColumn_ne_zero _ (measurableKernelProjector_ne_zero A h))

theorem measurable_kernelUnitVector (a d : ℕ) : Measurable (kernelUnitVector (a := a) (d := d)) :=
  (measurable_normalizeVector d).comp ((measurable_firstNonzeroColumn d d).comp
    (measurable_measurableKernelProjector a d))

end
end LowRank
