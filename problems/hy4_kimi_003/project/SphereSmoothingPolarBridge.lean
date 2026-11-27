import Mathlib.MeasureTheory.Constructions.HaarToSphere
import HaarRebalancingUniform

open MeasureTheory Set Metric

namespace Task006.SphereSmoothing

noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem polar_product_integral (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → V) :
    (∫ x, f x ∂μ) =
      ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), f (p.2.val • p.1.val)
        ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)) := by
  have hp := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
    (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f ((homeomorphUnitSphereProd E).symm p).val)
  have hsub : (∫ x : ({0}ᶜ : Set E), f x.val ∂μ.comap Subtype.val) = ∫ x, f x ∂μ := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl (fun x => f x),restrict_compl_singleton]
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply,
    homeomorphUnitSphereProd_symm_apply_coe,hsub] using hp

theorem polar_product_integrable (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → V} (hf : Integrable f μ) :
    Integrable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (p.2.val • p.1.val))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1))) := by
  have hsub : Integrable (fun x : ({0}ᶜ : Set E) => f x.val) (μ.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have hp := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (g := fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f ((homeomorphUnitSphereProd E).symm p).val)
    (Homeomorph.measurableEmbedding _)
  have hg : Integrable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
      f ((homeomorphUnitSphereProd E).symm p).val)
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1))) :=
    hp.mp (by simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hsub)
  simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hg

theorem polar_radial_integral (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → V}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) =
      ∫ r : Ioi (0 : ℝ), ∫ u : sphere (0 : E) 1, f (r.val • u.val) ∂μ.toSphere
        ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) := by
  rw [polar_product_integral]
  exact integral_prod_symm _ (polar_product_integrable μ hf)

theorem polar_real_radius_integral (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → V}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) =
      ∫ r in Ioi (0 : ℝ), r^(Module.finrank ℝ E-1) •
        (∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere) := by
  rw [polar_radial_integral μ hf]
  simp only [Measure.volumeIoiPow,ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const _).real_toNNReal)]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => Real.toNNReal (r^(Module.finrank ℝ E-1)) •
      (∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg hr.out.le _)]

end
end Task006.SphereSmoothing
