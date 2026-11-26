import LowRank.MeasurableKernelVector
import LowRank.OrderedSpectrumContinuity

/-! Measurable eigenvector choice for each ordered eigenvalue of a real
symmetric matrix. Repeated eigenvalues require no arbitrary basis choice. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

abbrev RealSymmetricMatrix (d : ℕ) := {A : Matrix (Fin d) (Fin d) ℝ // A.IsHermitian}

instance realSymmetricMatrixBorel (d : ℕ) : BorelSpace (RealSymmetricMatrix d) :=
  Subtype.borelSpace _

theorem OrderedMatrixSpectrum.column_eigenvector {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (j : Fin d) :
    A *ᵥ (fun i => sp.basis i j) = sp.value j • (fun i => sp.basis i j) := by
  ext i
  have h := congrFun (congrFun sp.mul_basis i) j
  simpa only [Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem OrderedMatrixSpectrum.column_ne_zero {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (j : Fin d) : (fun i => sp.basis i j) ≠ 0 := by
  have h := congrFun (congrFun sp.orthogonal j) j
  intro hz
  have hentries : ∀ i, sp.basis i j = 0 := fun i => congrFun hz i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hentries, mul_zero,
    Finset.sum_const_zero, Matrix.one_apply_eq] at h
  exact zero_ne_one h

def chosenEigenvector {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) : Fin d → ℝ :=
  kernelUnitVector (A - lam • 1)

theorem chosenEigenvector_eigen {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) :
    A *ᵥ chosenEigenvector A lam = lam • chosenEigenvector A lam := by
  have h := kernelUnitVector_in_kernel (A - lam • 1)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec] at h
  exact sub_eq_zero.mp h

theorem chosenEigenvector_dot_self {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (j : Fin d) :
    chosenEigenvector A (sp.value j) ⬝ᵥ chosenEigenvector A (sp.value j) = 1 := by
  apply kernelUnitVector_dot_self
  refine ⟨fun i => sp.basis i j, sp.column_ne_zero j, ?_⟩
  rw [Matrix.sub_mulVec, sp.column_eigenvector, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, sub_self]

theorem measurable_chosenEigenvector (d : ℕ) : Measurable
    (fun z : Matrix (Fin d) (Fin d) ℝ × ℝ => chosenEigenvector z.1 z.2) := by
  have h : Continuous (fun z : Matrix (Fin d) (Fin d) ℝ × ℝ => z.1 - z.2 • 1) := by fun_prop
  exact (measurable_kernelUnitVector d d).comp h.measurable

def orderedEigenvector {d : ℕ} (A : RealSymmetricMatrix d) (j : Fin d) : Fin d → ℝ :=
  chosenEigenvector A.1 ((orderedMatrixSpectrum A.2).value j)

theorem orderedEigenvector_dot_self {d : ℕ} (A : RealSymmetricMatrix d) (j : Fin d) :
    orderedEigenvector A j ⬝ᵥ orderedEigenvector A j = 1 :=
  chosenEigenvector_dot_self (orderedMatrixSpectrum A.2) j

theorem orderedEigenvector_eigen {d : ℕ} (A : RealSymmetricMatrix d) (j : Fin d) :
    A.1 *ᵥ orderedEigenvector A j = (orderedMatrixSpectrum A.2).value j • orderedEigenvector A j :=
  chosenEigenvector_eigen _ _

theorem measurable_orderedEigenvector (d : ℕ) (j : Fin d) :
    Measurable (fun A : RealSymmetricMatrix d => orderedEigenvector A j) := by
  have hlam : Measurable (fun A : RealSymmetricMatrix d => (orderedMatrixSpectrum A.2).value j) :=
    (continuous_ordered_eigenvalue (fun A : RealSymmetricMatrix d => A.1)
      (fun A => A.2) continuous_subtype_val j).measurable
  change Measurable ((fun z : Matrix (Fin d) (Fin d) ℝ × ℝ => chosenEigenvector z.1 z.2) ∘
    (fun A : RealSymmetricMatrix d => (A.1, (orderedMatrixSpectrum A.2).value j)))
  apply Measurable.comp (measurable_chosenEigenvector d)
  exact measurable_subtype_coe.prodMk hlam

end
end LowRank
