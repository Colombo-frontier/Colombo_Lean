import NCBall.NoisyHandleGeometry

/-! # The latent block Gaussian is the product of independent hidden/noise vectors -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

theorem gaussian_handle_product_synthesis (H : ℕ) :
    (Measure.pi (fun _ : Fin (H + 1) => euclideanGaussianLaw F)).map
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (H + 1) => F)).symm =
      euclideanGaussianLaw (HandleLatent F H) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (H + 1) => F)).symm
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hm : StronglyMeasurable (fun z : HandleLatent F H =>
      Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable e.continuous.measurable hm]
  have he (x : Fin (H + 1) → F) :
      Complex.exp ((⟪e x, t⟫_ℝ : ℂ) * Complex.I) =
        ∏ j, Complex.exp ((⟪x j, t j⟫_ℝ : ℂ) * Complex.I) := by
    have hi : ⟪e x, t⟫_ℝ = ∑ j, ⟪x j, t j⟫_ℝ := rfl
    rw [hi, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [he]
  letI : MeasureSpace F := ⟨euclideanGaussianLaw F⟩
  letI : SigmaFinite (volume : Measure F) := by
    change SigmaFinite (euclideanGaussianLaw F)
    infer_instance
  have hp : (∫ x : Fin (H + 1) → F, ∏ j, Complex.exp ((⟪x j, t j⟫_ℝ : ℂ) * Complex.I)
      ∂Measure.pi (fun _ : Fin (H + 1) => euclideanGaussianLaw F)) =
      ∏ j, ∫ x : F, Complex.exp ((⟪x, t j⟫_ℝ : ℂ) * Complex.I) ∂euclideanGaussianLaw F :=
    integral_fintype_prod_eq_prod (Fin (H + 1))
      (fun j (x : F) => Complex.exp ((⟪x, t j⟫_ℝ : ℂ) * Complex.I))
  rw [hp]
  change (∏ j, charFun (euclideanGaussianLaw F) (t j)) = _
  simp_rw [euclideanGaussian_characteristic]
  rw [← Complex.exp_sum]
  congr 1
  have hn : (∑ j, ‖t j‖ ^ 2) = ‖t‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ t).symm
  have hn' : (∑ j, (‖t j‖ : ℂ) ^ 2) = (‖t‖ : ℂ) ^ 2 := by exact_mod_cast hn
  rw [← Finset.sum_div, Finset.sum_neg_distrib, hn']

theorem gaussian_handle_blocks_independent (H : ℕ) :
    (euclideanGaussianLaw (HandleLatent F H)).map
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (H + 1) => F)) =
      Measure.pi (fun _ : Fin (H + 1) => euclideanGaussianLaw F) := by
  let e : HandleLatent F H ≃L[ℝ] (Fin (H + 1) → F) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (H + 1) => F)
  have hm : Measurable (e : HandleLatent F H → (Fin (H + 1) → F)) := e.continuous.measurable
  have hi : Measurable (e.symm : (Fin (H + 1) → F) → HandleLatent F H) := e.symm.continuous.measurable
  change (euclideanGaussianLaw (HandleLatent F H)).map e = _
  rw [← gaussian_handle_product_synthesis H, Measure.map_map hm hi]
  simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, Measure.map_id']

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem noisy_handle_reply {H : ℕ} (σ : ℝ) (h : Fin H) (a : F) (w : HandleLatent F H) :
    ⟪noisyHandleDirection F σ h a, w⟫_ℝ = ⟪a, w 0 + σ • w h.succ⟫_ℝ := by
  change ⟪handleBlock F 0 a + σ • handleBlock F h.succ a, w⟫_ℝ = _
  rw [inner_add_left, real_inner_smul_left, inner_add_right, real_inner_smul_right]
  have hi (j : Fin (H + 1)) : ⟪handleBlock F j a, w⟫_ℝ = ⟪a, w j⟫_ℝ := by
    classical
    rw [PiLp.inner_apply, Finset.sum_eq_single j]
    · simp [handleBlock]
    · intro k _ hkj
      simp [handleBlock, Pi.single_apply, hkj]
    · simp
  rw [hi, hi]

end NCBall
