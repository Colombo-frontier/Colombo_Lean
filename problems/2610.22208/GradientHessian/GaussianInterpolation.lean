import GradientHessian.GaussianLinearIBP
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Differentiation and continuity of Gaussian expectations along actual
paths of linear maps. Combined with integration by parts this gives the
Hessian-trace form of Gaussian interpolation, including degenerate maps. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter Set
open scoped InnerProductSpace BigOperators NNReal Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def linearGaussianExpectation (f : F → ℝ) (A : E →L[ℝ] F) : ℝ :=
  ∫ z, f (A z) ∂euclideanGaussianLaw E

theorem linearGaussianExpectation_lipschitz {f : F → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) :
    LipschitzWith ⟨(B : ℝ) * ∫ z : E, ‖z‖ ∂euclideanGaussianLaw E,
      mul_nonneg B.coe_nonneg (integral_nonneg fun _ => norm_nonneg _)⟩
      (linearGaussianExpectation E f) := by
  apply LipschitzWith.of_dist_le_mul
  intro A L
  have hiA : Integrable (fun z => f (A z)) (euclideanGaussianLaw E) :=
    lipschitz_integrable (hLip.comp A.lipschitz)
  have hiL : Integrable (fun z => f (L z)) (euclideanGaussianLaw E) :=
    lipschitz_integrable (hLip.comp L.lipschitz)
  have hbound (z : E) : ‖f (A z) - f (L z)‖ ≤ (B : ℝ) * ‖A - L‖ * ‖z‖ := by
    have h := hLip.dist_le_mul (A z) (L z)
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans (by
      simpa only [ContinuousLinearMap.sub_apply, mul_assoc] using
        mul_le_mul_of_nonneg_left ((A - L).le_opNorm z) B.coe_nonneg)
  rw [dist_eq_norm, linearGaussianExpectation, linearGaussianExpectation,
    ← integral_sub hiA hiL]
  calc
    _ ≤ ∫ z, ‖f (A z) - f (L z)‖ ∂euclideanGaussianLaw E := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ((B : ℝ) * ‖A - L‖) * ‖z‖ ∂euclideanGaussianLaw E :=
      integral_mono (hiA.sub hiL).norm ((norm_integrable E).const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul, dist_eq_norm]
      change (B : ℝ) * ‖A - L‖ * (∫ z : E, ‖z‖ ∂euclideanGaussianLaw E) =
        ((B : ℝ) * ∫ z : E, ‖z‖ ∂euclideanGaussianLaw E) * ‖A - L‖
      ring

theorem linearGaussianExpectation_hasDerivAt {f : F → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith B f)
    {A A' : ℝ → E →L[ℝ] F} {t : ℝ}
    (hA : ∀ᶠ s in 𝓝 t, HasDerivAt A (A' s) s) (hA' : ContinuousAt A' t) :
    HasDerivAt (fun s => linearGaussianExpectation E f (A s))
      (∫ z, fderiv ℝ f (A t z) (A' t z) ∂euclideanGaussianLaw E) t := by
  have hloc : ∀ᶠ s in 𝓝 t, ‖A' s‖ < ‖A' t‖ + 1 :=
    hA'.norm.eventually (gt_mem_nhds (by linarith : ‖A' t‖ < ‖A' t‖ + 1))
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp (hA.and hloc)
  let H : ℝ → E → ℝ := fun s z => f (A s z)
  let H' : ℝ → E → ℝ := fun s z => fderiv ℝ f (A s z) (A' s z)
  let bound : E → ℝ := fun z => ((B : ℝ) * (‖A' t‖ + 1)) * ‖z‖
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (H s) (euclideanGaussianLaw E) :=
    Eventually.of_forall (fun s => (hf.continuous.comp (A s).continuous).aestronglyMeasurable)
  have hi : Integrable (H t) (euclideanGaussianLaw E) :=
    lipschitz_integrable (hLip.comp (A t).lipschitz)
  have hdmeas : AEStronglyMeasurable (H' t) (euclideanGaussianLaw E) :=
    (((hf.continuous_fderiv (by norm_num)).comp (A t).continuous).clm_apply
      (A' t).continuous).aestronglyMeasurable
  have hb : ∀ᵐ z ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε, ‖H' s z‖ ≤ bound z := by
    apply ae_of_all
    intro z s hs
    have hp := (hlocal s hs).2.le
    calc
      ‖H' s z‖ ≤ ‖fderiv ℝ f (A s z)‖ * ‖A' s z‖ := (fderiv ℝ f _).le_opNorm _
      _ ≤ (B : ℝ) * ((‖A' t‖ + 1) * ‖z‖) :=
        mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hLip)
          (((A' s).le_opNorm z).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg z)))
          (norm_nonneg _) B.coe_nonneg
      _ = bound z := by dsimp [bound]; ring
  have hd : ∀ᵐ z ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε,
      HasDerivAt (fun r => H r z) (H' s z) s := by
    apply ae_of_all
    intro z s hs
    have hlin := ((hlocal s hs).1.clm_apply (hasDerivAt_const s z))
    simp only [map_zero, add_zero] at hlin
    exact (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hlin
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hm hi hdmeas hb
    ((norm_integrable E).const_mul _) hd).2

theorem gaussian_interpolation_hasDerivAt {f : F → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    {A A' : ℝ → E →L[ℝ] F} {t : ℝ}
    (hA : ∀ᶠ s in 𝓝 t, HasDerivAt A (A' s) s) (hA' : ContinuousAt A' t) :
    HasDerivAt (fun s => linearGaussianExpectation E f (A s))
      (∫ z, ∑ i, fderiv ℝ (fderiv ℝ f) (A t z)
        (A t (stdOrthonormalBasis ℝ E i)) (A' t (stdOrthonormalBasis ℝ E i))
        ∂euclideanGaussianLaw E) t := by
  have h := linearGaussianExpectation_hasDerivAt E (hf.of_le (by norm_num)) hLip hA hA'
  have he := gaussian_linear_ibp E hf hLip hH (A t) (A' t) 0
  simp only [zero_add] at he
  rwa [he] at h

end GradientHessian.GaussianConcentration
