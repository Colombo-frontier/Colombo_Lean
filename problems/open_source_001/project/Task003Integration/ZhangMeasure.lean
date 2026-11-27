import Task003Integration.ZhangMeasureCore
import Nonsmooth.GaussianPrior

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Task003Integration
noncomputable section

def halfRow {d : ℕ} (a : Nonsmooth.Feasible (EuclideanSpace ℝ (Fin d)) 2) : Fin d → ℝ :=
  fun j => a.val j / 2

def halfRows {d k : ℕ}
    (a : Nonsmooth.BoundedSupportRows (EuclideanSpace ℝ (Fin d)) (Fin k)) :
    Fin k → Fin d → ℝ := fun i => halfRow (a i)

theorem halfRow_measurable (d : ℕ) : Measurable (@halfRow d) := by
  unfold halfRow
  fun_prop

theorem halfRows_measurable (d k : ℕ) : Measurable (@halfRows d k) := by
  apply measurable_pi_lambda
  intro i
  exact (halfRow_measurable d).comp (measurable_pi_apply i)

theorem nonsmooth_gaussian_eq_std (d : ℕ) :
    Nonsmooth.euclideanGaussianLaw (EuclideanSpace ℝ (Fin d)) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := rfl

theorem nonsmooth_truncated_eq_map (d : ℕ) :
    Nonsmooth.truncatedGaussianLaw (EuclideanSpace ℝ (Fin d)) =
      (PaperTruncatedGaussianRows.truncatedLaw d).map
        (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) := by
  rw [truncatedLaw_to_euclidean]
  simp only [Nonsmooth.truncatedGaussianLaw, nonsmooth_gaussian_eq_std,
    finrank_euclideanSpace_fin]

/-- Push the actual subtype-valued truncated law back into the ambient space. -/
theorem nonsmooth_vector_ambient_map (d : ℕ) [NeZero d] :
    (Nonsmooth.truncatedGaussianVectorLaw (EuclideanSpace ℝ (Fin d))).map
        (Subtype.val : Nonsmooth.Feasible (EuclideanSpace ℝ (Fin d))
          (2 * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) →
          EuclideanSpace ℝ (Fin d)) =
      Nonsmooth.truncatedGaussianLaw (EuclideanSpace ℝ (Fin d)) := by
  rw [Nonsmooth.truncatedGaussianVectorLaw]
  erw [map_comap_subtype_coe (isClosed_le continuous_norm continuous_const).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem Nonsmooth.truncatedGaussianLaw_supported

/-- The rescaled bounded row law has the expected ambient pushforward. -/
theorem nonsmooth_row_ambient_map (d : ℕ) [NeZero d] :
    (Nonsmooth.gaussianSupportRowLaw (EuclideanSpace ℝ (Fin d))).map
        (Subtype.val : Nonsmooth.Feasible (EuclideanSpace ℝ (Fin d)) 2 →
          EuclideanSpace ℝ (Fin d)) =
      (Nonsmooth.truncatedGaussianLaw (EuclideanSpace ℝ (Fin d))).map
        (fun z => (Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))))⁻¹ • z) := by
  rw [Nonsmooth.gaussianSupportRowLaw,
    Measure.map_map measurable_subtype_coe Nonsmooth.gaussianScaleRow_measurable]
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin d) =>
      (Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))))⁻¹ • z) := by
    fun_prop
  rw [← nonsmooth_vector_ambient_map d, Measure.map_map hm measurable_subtype_coe]
  rfl

theorem halfRow_map_law (d : ℕ) [NeZero d] :
    (Nonsmooth.gaussianSupportRowLaw (EuclideanSpace ℝ (Fin d))).map halfRow =
      PaperTruncatedGaussianRows.rowLaw d := by
  let h : EuclideanSpace ℝ (Fin d) → Fin d → ℝ := fun z j => z j / 2
  have hm : Measurable h := by dsimp [h]; fun_prop
  have hs : Measurable (fun z : EuclideanSpace ℝ (Fin d) =>
      (Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))))⁻¹ • z) := by fun_prop
  have ht : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) := by fun_prop
  change (Nonsmooth.gaussianSupportRowLaw (EuclideanSpace ℝ (Fin d))).map (h ∘ Subtype.val) = _
  rw [← Measure.map_map hm measurable_subtype_coe, nonsmooth_row_ambient_map d,
    Measure.map_map hm hs, nonsmooth_truncated_eq_map,
    Measure.map_map (hm.comp hs) ht]
  congr 1
  funext b j
  simp only [Function.comp_apply, h, finrank_euclideanSpace_fin,
    PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply,
    PaperTruncatedGaussianRows.scaleRow]
  ring

theorem halfRows_map_law (d k : ℕ) [NeZero d] :
    (Nonsmooth.gaussianSupportPrior (EuclideanSpace ℝ (Fin d)) k).map halfRows =
      PaperTruncatedGaussianRows.rowsLaw d k := by
  letI : IsProbabilityMeasure (PaperTruncatedGaussianRows.rowLaw d) :=
    PaperTruncatedGaussianRows.rowLaw_isProbability d (Nat.pos_of_ne_zero (NeZero.ne d))
  have hrow : MeasurePreserving halfRow
      (Nonsmooth.gaussianSupportRowLaw (EuclideanSpace ℝ (Fin d)))
      (PaperTruncatedGaussianRows.rowLaw d) :=
    ⟨halfRow_measurable d, halfRow_map_law d⟩
  exact (measurePreserving_pi
    (fun _ : Fin k => Nonsmooth.gaussianSupportRowLaw (EuclideanSpace ℝ (Fin d)))
    (fun _ : Fin k => PaperTruncatedGaussianRows.rowLaw d)
    (fun _ => hrow)).map_eq

end
end Task003Integration
