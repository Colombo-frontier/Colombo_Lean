import UpperSmoothingSecant

/-!
Differentiability of actual uniform-ball smoothing, using Rademacher's theorem
and differentiation under the integral. The forthcoming translation proof uses
a conservative factor `2d`, sufficient for the same main upper bound. It does
not claim the manuscript's sharper factor `d` has already been checked.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal

namespace Task006.Full

/-- The actual averaged derivative of a Lipschitz function, at the same
uniform-ball distribution used by the algorithm. -/
noncomputable def ballSmoothDerivative {d : ℕ} (f : Space d → ℝ)
    (ρ : ℝ) (x : Space d) : Space d →L[ℝ] ℝ :=
  ∫ u, fderiv ℝ f (x + ρ • u) ∂unitBallLaw d

theorem ballSmooth_hasFDerivAt_global {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) (x : Space d) :
    Integrable (fun u => fderiv ℝ f (x + ρ • u)) (unitBallLaw d) ∧
      HasFDerivAt (ballSmooth f ρ) (ballSmoothDerivative f ρ x) x := by
  have hq : QuasiMeasurePreserving (fun u : Space d => x + ρ • u) volume volume :=
    (measurePreserving_add_left volume x).quasiMeasurePreserving.comp
      (quasiMeasurePreserving_smul volume hρ.ne')
  have hdvol : ∀ᵐ u ∂(volume : Measure (Space d)), DifferentiableAt ℝ f (x + ρ • u) :=
    hq.ae (hf.ae_differentiableAt (μ := volume))
  have hd : ∀ᵐ u ∂unitBallLaw d, DifferentiableAt ℝ f (x + ρ • u) :=
    Measure.ae_smul_measure (ae_restrict_of_ae hdvol) _
  have hmeas : ∀ y ∈ (univ : Set (Space d)),
      AEStronglyMeasurable (fun u => f (y + ρ • u)) (unitBallLaw d) := by
    intro y _
    exact (hf.continuous.comp (by fun_prop)).measurable.aestronglyMeasurable
  have hi : Integrable (fun u => f (x + ρ • u)) (unitBallLaw d) := by
    exact ballSmooth_integrable (R := ‖x‖ + ρ) hf.continuous.continuousOn hρ.le
      (by linarith [norm_nonneg x]) (by linarith)
  have hdm : AEStronglyMeasurable (fun u => fderiv ℝ f (x + ρ • u)) (unitBallLaw d) :=
    ((measurable_fderiv ℝ f).comp (by fun_prop)).aestronglyMeasurable
  have hlip : ∀ᵐ u ∂unitBallLaw d, ∀ y ∈ (univ : Set (Space d)),
      ‖f (y + ρ • u) - f (x + ρ • u)‖ ≤ (L : ℝ) * ‖y - x‖ := by
    exact ae_of_all _ (fun u y _ => by
      simpa only [add_sub_add_right_eq_sub] using hf.norm_sub_le (y + ρ • u) (x + ρ • u))
  have hdiff : ∀ᵐ u ∂unitBallLaw d,
      HasFDerivAt (fun y => f (y + ρ • u)) (fderiv ℝ f (x + ρ • u)) x := by
    filter_upwards [hd] with u hu
    convert! hu.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (ρ • u)) using 1
  exact hasFDerivAt_integral_of_dominated_loc_of_lip'
    (s := univ) (bound := fun _ => (L : ℝ)) univ_mem hmeas hi hdm hlip
    (integrable_const _) hdiff

/-- Exact change of variables from normalized unit-ball sampling to the
translated physical ball. It is valid for every Bochner-valued integrand. -/
theorem unitBallLaw_integral_affine {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (g : Space d → V)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Space d) :
    (∫ u, g (x + ρ • u) ∂unitBallLaw d) =
      (volume.real (closedBall (0 : Space d) ρ))⁻¹ •
        ∫ y in closedBall x ρ, g y := by
  have hpre : (fun y : Space d => x + y) ⁻¹' closedBall x ρ =
      closedBall (0 : Space d) ρ := by
    ext y
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have htrans := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding g (closedBall x ρ)
  rw [hpre] at htrans
  unfold unitBallLaw
  rw [integral_smul_measure, setIntegral_comp_smul_of_pos volume (fun y => g (x + y))
    (closedBall (0 : Space d) 1) hρ]
  rw [_root_.smul_closedBall' hρ.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hρ, mul_one, htrans,
    smul_smul]
  congr 1
  rw [addHaar_real_closedBall' volume (0 : Space d) hρ.le]
  simp only [measureReal_def, ENNReal.toReal_inv, mul_inv_rev]

theorem ballSmoothDerivative_ballIntegral {d : ℕ} (f : Space d → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Space d) :
    ballSmoothDerivative f ρ x = (volume.real (closedBall (0 : Space d) ρ))⁻¹ •
      ∫ y in closedBall x ρ, fderiv ℝ f y :=
  unitBallLaw_integral_affine (fderiv ℝ f) hρ x

#print axioms ballSmooth_hasFDerivAt_global
#print axioms unitBallLaw_integral_affine

end Task006.Full
