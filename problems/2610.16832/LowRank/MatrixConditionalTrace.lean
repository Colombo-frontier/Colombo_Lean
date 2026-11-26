import LowRank.MatrixConditionalOrder
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! A transcript-measurable matrix may be pulled through the conditional
expectation of a trace product. The projector corollary derives the needed
integrability from the uniform entry bound for orthogonal projectors. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {Ω n : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
  [Fintype n] [DecidableEq n]

theorem condExp_trace_mul (P A : Ω → Matrix n n ℝ)
    (hP : ∀ i j, AEStronglyMeasurable[m] (fun ω => P ω i j) μ)
    (hA : EntryIntegrable A μ)
    (hPA : ∀ i j, Integrable (fun ω => P ω i j * A ω j i) μ) :
    μ[fun ω => (P ω * A ω).trace | m] =ᵐ[μ]
      (fun ω => (P ω * matrixCondMean μ m A ω).trace) := by
  have hs := condExp_finite_weighted_sum m μ
    (fun ij : n × n => fun ω => P ω ij.1 ij.2 * A ω ij.2 ij.1)
    (fun ij => hPA ij.1 ij.2) (fun _ => 1)
  simp only [one_mul] at hs
  have he : ∀ ij : n × n, ∀ᵐ ω ∂μ,
      μ[fun z => P z ij.1 ij.2 * A z ij.2 ij.1 | m] ω =
        P ω ij.1 ij.2 * matrixCondMean μ m A ω ij.2 ij.1 := by
    intro ij
    exact condExp_mul_of_aestronglyMeasurable_left (hP ij.1 ij.2)
      (hPA ij.1 ij.2) (hA ij.2 ij.1)
  have hall := (ae_all_iff).mpr he
  have ht : ∀ M N : Matrix n n ℝ, (M * N).trace =
      ∑ ij : n × n, M ij.1 ij.2 * N ij.2 ij.1 := by
    intros
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [ht]
  filter_upwards [hs, hall] with ω hsum hterm
  rw [hsum]
  exact Finset.sum_congr rfl (fun ij _ => hterm ij)

theorem projector_mul_entryIntegrable (P A : Ω → Matrix n n ℝ)
    (hPmeas : ∀ i j, AEStronglyMeasurable (fun ω => P ω i j) μ)
    (hP : ∀ᵐ ω ∂μ, IsOrthogonalProjector (P ω)) (hA : EntryIntegrable A μ) :
    ∀ i j, Integrable (fun ω => P ω i j * A ω j i) μ := by
  intro i j
  apply (hA j i).bdd_mul' (hPmeas i j)
  filter_upwards [hP] with ω hω
  exact hω.entry_norm_le_one i j

theorem condExp_projector_trace_mul (hm : m ≤ mΩ) (P A : Ω → Matrix n n ℝ)
    (hPmeas : ∀ i j, AEStronglyMeasurable[m] (fun ω => P ω i j) μ)
    (hP : ∀ᵐ ω ∂μ, IsOrthogonalProjector (P ω)) (hA : EntryIntegrable A μ) :
    μ[fun ω => (P ω * A ω).trace | m] =ᵐ[μ]
      (fun ω => (P ω * matrixCondMean μ m A ω).trace) := by
  apply condExp_trace_mul m μ P A hPmeas hA
  exact projector_mul_entryIntegrable μ P A (fun i j => (hPmeas i j).mono hm) hP hA

end
end LowRank
