import SphereSmoothingCutoffDerivativeAE
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

theorem integrable_of_bounded_ball_support {d : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {g : EuclideanSpace ℝ (Fin d) → V} {C R : ℝ}
    (hm : AEStronglyMeasurable g volume) (hb : ∀ z, ‖g z‖ ≤ C)
    (hz : ∀ z, z ∉ closedBall 0 R → g z=0) : Integrable g volume := by
  have hi : IntegrableOn g (closedBall 0 R) volume :=
    IntegrableOn.of_bound measure_closedBall_lt_top hm.restrict C (ae_of_all _ hb)
  have heq : (closedBall 0 R).indicator g=g := by
    funext z
    by_cases h : z ∈ closedBall 0 R
    · exact indicator_of_mem h g
    · rw [indicator_of_notMem h, hz z h]
  rw [← heq]
  exact hi.integrable_indicator measurableSet_closedBall

def cutoffWeightedDerivative {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (ρ ε : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  radialCutoff ρ ε z • fderiv ℝ f z

def openAnnulus {d : ℕ} (ρ ε : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {z | ρ < ‖z‖ ∧ ‖z‖ < ρ+ε}

theorem measurableSet_openAnnulus {d : ℕ} (ρ ε : ℝ) : MeasurableSet (openAnnulus (d := d) ρ ε) :=
  ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet

def annularNormal {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (ρ ε : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  (openAnnulus ρ ε).indicator (fun z => f z • (‖z‖⁻¹ • innerSL ℝ z)) z

theorem cutoffWeightedDerivative_integrable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {ρ ε : ℝ} (hε : 0 < ε) :
    Integrable (cutoffWeightedDerivative f ρ ε) volume := by
  have hm : Measurable (cutoffWeightedDerivative f ρ ε) :=
    (radialCutoff_lipschitz (E := EuclideanSpace ℝ (Fin d)) hε).continuous.measurable.smul (measurable_fderiv ℝ f)
  apply integrable_of_bounded_ball_support (R := ρ+ε) hm.aestronglyMeasurable (C := (K:ℝ))
  · intro z
    rw [cutoffWeightedDerivative, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (radialCutoff_nonneg ρ ε z)]
    calc
      _ ≤ 1*(K:ℝ) := mul_le_mul (radialCutoff_le_one ρ ε z)
        (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · intro z hz
    have hn : ρ+ε ≤ ‖z‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using (le_of_lt (show ρ+ε < ‖z‖ by simpa only [mem_closedBall,dist_zero_right,not_le] using hz))
    simp only [cutoffWeightedDerivative, radialCutoff_eq_zero hε hn, zero_smul]

theorem annularNormal_integrable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Integrable (annularNormal f ρ ε) volume := by
  let C : ℝ := |f 0|+(K:ℝ)*(ρ+ε)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn : Measurable (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖⁻¹ • innerSL ℝ z) :=
    measurable_norm.inv.smul (innerSL ℝ).continuous.measurable
  have hm : Measurable (annularNormal f ρ ε) :=
    (hf.continuous.measurable.smul hn).indicator (measurableSet_openAnnulus ρ ε)
  apply integrable_of_bounded_ball_support (R := ρ+ε) hm.aestronglyMeasurable (C := C)
  · intro z
    by_cases hz : z ∈ openAnnulus ρ ε
    · have hzn : 0 < ‖z‖ := hρ.trans hz.1
      have hfb : |f z| ≤ C := by
        have hd := hf.norm_sub_le z 0
        simp only [Real.norm_eq_abs, sub_zero] at hd
        have hh : |f z| ≤ |f z-f 0|+|f 0| := by simpa only [sub_add_cancel] using abs_add_le (f z-f 0) (f 0)
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left hz.2.le K.coe_nonneg]
      rw [annularNormal, indicator_of_mem hz, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, innerSL_apply_norm, abs_of_pos (inv_pos.2 hzn), inv_mul_cancel₀ hzn.ne', mul_one]
      exact hfb
    · simp only [annularNormal, indicator_of_notMem hz, norm_zero]
      exact hC
  · intro z hz
    have hnot : z ∉ openAnnulus ρ ε := fun hh => hz (by simpa only [mem_closedBall,dist_zero_right] using hh.2.le)
    exact indicator_of_notMem hnot _

/-- Exact radial integration by parts for the original Lipschitz f. This is
the pre-limit ball/sphere boundary identity, with every term integrable. -/
theorem cutoff_weak_annulus_identity {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    (∫ z, cutoffWeightedDerivative f ρ ε z) = ε⁻¹ • ∫ z, annularNormal f ρ ε z := by
  obtain ⟨⟨K',hlip⟩,hcompact⟩ := radialCutoff_product_regular hf hρ hε
  have hzero := integral_fderiv_lipschitz_compactSupport_eq_zero hlip hcompact
  have hW := cutoffWeightedDerivative_integrable hf hε (ρ := ρ)
  have hS := annularNormal_integrable hf hρ hε
  have hcoefficient (z : EuclideanSpace ℝ (Fin d)) :
      f z • radialCutoffDerivative ρ ε z = -ε⁻¹ • annularNormal f ρ ε z := by
    by_cases hz : z ∈ openAnnulus ρ ε
    · have hh : ρ < ‖z‖ ∧ ‖z‖ < ρ+ε := hz
      rw [radialCutoffDerivative, if_pos hh, annularNormal, indicator_of_mem hz]
      simp only [smul_smul, mul_inv_rev]
      congr 1
      ring
    · have hh : ¬(ρ < ‖z‖ ∧ ‖z‖ < ρ+ε) := hz
      simp only [radialCutoffDerivative, if_neg hh, annularNormal, indicator_of_notMem hz, smul_zero]
  have hfd : ∀ᵐ z : EuclideanSpace ℝ (Fin d), DifferentiableAt ℝ f z := hf.ae_differentiableAt
  have heq : (fderiv ℝ (fun z => f z*radialCutoff ρ ε z)) =ᵐ[volume]
      (fun z => cutoffWeightedDerivative f ρ ε z - ε⁻¹ • annularNormal f ρ ε z) := by
    filter_upwards [hfd,radialCutoff_hasFDerivAt_ae (d := d) hρ hε] with z hz hη
    change fderiv ℝ (f*radialCutoff (E := EuclideanSpace ℝ (Fin d)) ρ ε) z = _
    rw [(hz.hasFDerivAt.mul hη).fderiv, hcoefficient]
    simp only [cutoffWeightedDerivative, sub_eq_add_neg]
    module
  have hint := integral_congr_ae heq
  have hSi : Integrable (fun z => ε⁻¹ • annularNormal f ρ ε z) volume := by
    convert! Integrable.smul ε⁻¹ hS using 1
  rw [hzero.2,integral_sub hW hSi,integral_smul] at hint
  exact sub_eq_zero.mp hint.symm

end
end Task006.SphereSmoothing
