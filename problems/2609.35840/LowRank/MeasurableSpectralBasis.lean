import LowRank.MeasurableSpectralStep

/-! Recursively split the smallest eigendirection to obtain an ordered
orthogonal diagonalization whose basis is a measurable function of the matrix. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def extendOrderedSpectrum {d : ℕ} (A : RealSymmetricMatrix (d + 1))
    (sp : OrderedMatrixSpectrum (spectralTail A).1) : OrderedMatrixSpectrum A.1 where
  value := Fin.cons ((orderedMatrixSpectrum A.2).value 0) sp.value
  basis := spectralGauge A * leadingBlock 1 sp.basis
  increasing := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro _; exact le_rfl
    · intro _; exact spectralTail_eigenvalue_ge_min A sp j
    · intro h
      have h' : i.val + 1 ≤ 0 := by simpa using h
      omega
    · intro h; exact sp.increasing (by simpa using h)
  orthogonal := by
    calc
      _ = (leadingBlock 1 sp.basis)ᵀ * ((spectralGauge A)ᵀ * spectralGauge A) *
          leadingBlock 1 sp.basis := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [spectralGauge_orthogonal, Matrix.mul_one, leadingBlock_orthogonal _ sp.orthogonal]
  diagonalizes := by
    calc
      _ = (leadingBlock 1 sp.basis)ᵀ * ((spectralGauge A)ᵀ * A.1 * spectralGauge A) *
          leadingBlock 1 sp.basis := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [spectralGauge_diagonal_block, leadingBlock_transpose, leadingBlock_mul,
          leadingBlock_mul, sp.diagonalizes, one_mul, mul_one, leadingBlock_diagonal]

def canonicalOrderedSpectrum : (d : ℕ) → (A : RealSymmetricMatrix d) → OrderedMatrixSpectrum A.1
  | 0, _ => {
      value := Fin.elim0
      basis := 1
      increasing := by intro i; exact Fin.elim0 i
      orthogonal := by simp
      diagonalizes := by ext i; exact Fin.elim0 i }
  | d + 1, A => extendOrderedSpectrum A (canonicalOrderedSpectrum d (spectralTail A))

theorem canonicalOrderedSpectrum_value {d : ℕ} (A : RealSymmetricMatrix d) :
    (canonicalOrderedSpectrum d A).value = (orderedMatrixSpectrum A.2).value :=
  (canonicalOrderedSpectrum d A).value_unique (orderedMatrixSpectrum A.2)

theorem measurable_canonical_spectral_basis (d : ℕ) :
    Measurable (fun A : RealSymmetricMatrix d => (canonicalOrderedSpectrum d A).basis) := by
  induction d with
  | zero => exact measurable_const
  | succ d ih =>
      have hU := measurable_spectralGauge d
      have htail := ih.comp (measurable_spectralTail d)
      have hblock : Measurable (fun A : RealSymmetricMatrix (d + 1) =>
          leadingBlock 1 (canonicalOrderedSpectrum d (spectralTail A)).basis) :=
        (measurable_leadingBlock d).comp (measurable_const.prodMk htail)
      change Measurable (fun A : RealSymmetricMatrix (d + 1) => spectralGauge A *
        leadingBlock 1 (canonicalOrderedSpectrum d (spectralTail A)).basis)
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      simp only [Matrix.mul_apply]
      fun_prop

end
end LowRank
