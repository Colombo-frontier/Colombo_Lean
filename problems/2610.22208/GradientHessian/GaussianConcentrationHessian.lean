import GradientHessian.GaussianConcentrationDerivative

/-! Vector-valued differentiation of Gaussian smoothing and the resulting
exact Hessian commutation formula. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter
open scoped NNReal Topology

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def vectorMehler (ρ : ℝ) (f : E → V) (x : E) : V :=
  ∫ z, f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem vector_lipschitz_integrable {B : ℝ≥0} {f : E → V} (hf : LipschitzWith B f) :
    Integrable f (euclideanGaussianLaw E) := by
  have hi := (integrable_const ‖f 0‖).add ((norm_integrable E).const_mul (B : ℝ))
  refine hi.mono' hf.continuous.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hd := hf.dist_le_mul x 0
  rw [dist_zero_right, dist_eq_norm] at hd
  have hn := norm_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at hn
  change ‖f x‖ ≤ ‖f 0‖ + (B : ℝ) * ‖x‖
  linarith only [hd, hn]

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem vector_affine_integrable {B : ℝ≥0} {f : E → V} (hf : LipschitzWith B f)
    (a : ℝ) (c : E) : Integrable (fun z => f (c + a • z)) (euclideanGaussianLaw E) := by
  have hl : LipschitzWith ‖a‖₊ (fun z : E => c + a • z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, coe_nnnorm]
    exact le_rfl
  exact vector_lipschitz_integrable (hf.comp hl)

omit [CompleteSpace V] in
theorem vectorMehler_hasFDerivAt {B : ℝ≥0} {f : E → V}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith B f) (ρ : ℝ) (x : E) :
    HasFDerivAt (vectorMehler ρ f)
      (ρ • ∫ z, fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
        ∂euclideanGaussianLaw E) x := by
  let σ := Real.sqrt (1 - ρ ^ 2)
  let F : E → E → V := fun y z => f (ρ • y + σ • z)
  let F' : E → E → E →L[ℝ] V := fun y z => ρ • fderiv ℝ f (ρ • y + σ • z)
  have hdiff (y z : E) : HasFDerivAt (fun w => F w z) (F' y z) y := by
    have hi := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul ρ).add_const (σ • z)
    have ho := (hf.differentiable (by norm_num) (ρ • y + σ • z)).hasFDerivAt.comp y hi
    convert ho using 1
    ext u
    simp only [F', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul]
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (euclideanGaussianLaw E) := by
    apply Eventually.of_forall
    intro y
    exact (hf.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  have h'int : Integrable (F x) (euclideanGaussianLaw E) :=
    vector_affine_integrable hLip σ (ρ • x)
  have h'dmeas : AEStronglyMeasurable (F' x) (euclideanGaussianLaw E) := by
    apply Continuous.aestronglyMeasurable
    exact continuous_const.smul ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_const.smul continuous_id)))
  have hbnd : ∀ᵐ z ∂euclideanGaussianLaw E, ∀ y ∈ Metric.ball x 1,
      ‖F' y z‖ ≤ ‖ρ‖ * (B : ℝ) := by
    apply ae_of_all
    intro z y _
    dsimp [F']
    calc
      ‖ρ • fderiv ℝ f (ρ • y + σ • z)‖ =
          ‖ρ‖ * ‖fderiv ℝ f (ρ • y + σ • z)‖ := norm_smul ρ (fderiv ℝ f (ρ • y + σ • z))
      _ ≤ ‖ρ‖ * (B : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg ρ)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := euclideanGaussianLaw E)
    (F := F) (F' := F') (bound := fun _ => ‖ρ‖ * (B : ℝ))
    (by norm_num : (0 : ℝ) < 1) hmeas h'int h'dmeas hbnd (integrable_const _)
    (ae_of_all _ fun z y _ => hdiff y z)
  dsimp [F'] at hd
  rw [integral_smul] at hd
  exact hd

theorem mehler_hessian {B C : ℝ≥0} {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (ρ : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (mehler E ρ f)) x =
      ρ ^ 2 • ∫ z, fderiv ℝ (fderiv ℝ f) (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
        ∂euclideanGaussianLaw E := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDLip : LipschitzWith C (fderiv ℝ f) :=
    lipschitzWith_of_nnnorm_fderiv_le (hD.differentiable (by norm_num))
      (fun x => by exact_mod_cast hH x)
  have he : fderiv ℝ (mehler E ρ f) = fun y => ρ • vectorMehler ρ (fderiv ℝ f) y :=
    funext (mehler_fderiv (hf.of_le (by norm_num)) hLip ρ)
  rw [he, ((vectorMehler_hasFDerivAt hD hDLip ρ x).const_smul ρ).fderiv,
    smul_smul, pow_two]

end GradientHessian.GaussianConcentration
