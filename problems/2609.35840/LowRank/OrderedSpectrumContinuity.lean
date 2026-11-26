import LowRank.MatrixEntryMass

/-! Ordered eigenvalues of a continuous family of real symmetric matrices
are continuous, proved by elementary perturbation bounds and Loewner order. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

def OrderedMatrixSpectrum.shift {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (c : ℝ) : OrderedMatrixSpectrum (A + c • 1) where
  value := fun i => sp.value i + c
  basis := sp.basis
  increasing := fun _ _ hij => add_le_add_right (sp.increasing hij) c
  orthogonal := sp.orthogonal
  diagonalizes := by
    rw [Matrix.mul_add, Matrix.add_mul, sp.diagonalizes, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, sp.orthogonal, ← real_diagonal_const, Matrix.diagonal_add]

theorem ordered_eigenvalue_abs_sub_le {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin d) :
    |(orderedMatrixSpectrum hA).value i - (orderedMatrixSpectrum hB).value i| ≤
      matrixEntryMass (A - B) := by
  have h₁ := ordered_eigenvalue_mono (orderedMatrixSpectrum hA)
    ((orderedMatrixSpectrum hB).shift (matrixEntryMass (A - B)))
    (loewner_le_shift_entryMass hA hB) i
  have h₂ := ordered_eigenvalue_mono (orderedMatrixSpectrum hB)
    ((orderedMatrixSpectrum hA).shift (matrixEntryMass (B - A)))
    (loewner_le_shift_entryMass hB hA) i
  simp only [OrderedMatrixSpectrum.shift] at h₁ h₂
  rw [matrixEntryMass_sub_comm B A] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuous_ordered_eigenvalue {α : Type*} [TopologicalSpace α] {d : ℕ}
    (A : α → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hcont : Continuous A) (i : Fin d) :
    Continuous (fun x => (orderedMatrixSpectrum (hA x)).value i) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun y => ?_)
  · have hc : Continuous (fun y => matrixEntryMass (A y - A x)) :=
      (continuous_matrixEntryMass d d).comp (hcont.sub continuous_const)
    simpa only [sub_self, matrixEntryMass_zero] using hc.tendsto x
  · simpa only [Real.norm_eq_abs] using ordered_eigenvalue_abs_sub_le (hA y) (hA x) i

end
end LowRank
