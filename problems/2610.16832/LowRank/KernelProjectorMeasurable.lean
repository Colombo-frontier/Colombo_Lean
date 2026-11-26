import LowRank.KernelProjector
import LowRank.MatrixExpectation
import LowRank.GaussianModel
import Mathlib.Topology.Instances.Matrix

/-! The explicit projector is measurable everywhere and uniformly bounded
entrywise. Thus its entries are integrable under every probability law. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem measurable_real_matrix_inverse : Measurable (fun A : Matrix n n ℝ => A⁻¹) := by
  have hd : Continuous (fun A : Matrix n n ℝ => A.det) := continuous_id.matrix_det
  have ha : Continuous (fun A : Matrix n n ℝ => A.adjugate) := continuous_id.matrix_adjugate
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact hd.measurable.inv.smul ha.measurable

theorem measurable_leftKernelProjector : Measurable (leftKernelProjector (m := m) (n := n)) := by
  have hg : Continuous (fun D : Matrix m n ℝ => Dᵀ * D) := by fun_prop
  have hi : Measurable (fun D : Matrix m n ℝ => (Dᵀ * D)⁻¹) :=
    measurable_real_matrix_inverse.comp hg.measurable
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [leftKernelProjector, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem leftKernelProjector_entryIntegrable (μ : Measure (Matrix m n ℝ)) [IsProbabilityMeasure μ] :
    EntryIntegrable leftKernelProjector μ := by
  intro i j
  have hm : Measurable (fun D : Matrix m n ℝ => leftKernelProjector D i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
  exact (integrable_const (1 : ℝ)).mono' hm.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun D => (leftKernelProjector_isProjector D).entry_norm_le_one i j))

end
end LowRank
