import NCBall.GaussianHilbert
import NCBall.GaussianSmallBall

/-! # Orthogonal linear coordinates of an actual standard Gaussian -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators NNReal
namespace NCBall

theorem diagonalGaussian_centered_characteristic {k : ℕ} (v : Fin k → ℝ≥0) (t : Fin k → ℝ) :
    (∫ x, Complex.exp (((∑ i, t i * x i : ℝ) : ℂ) * Complex.I)
      ∂diagonalGaussian (fun _ => 0) v) =
      Complex.exp (-((∑ i, (v i : ℝ) * (t i) ^ 2 : ℝ) : ℂ) / 2) := by
  have he (x : Fin k → ℝ) :
      Complex.exp (((∑ i, t i * x i : ℝ) : ℂ) * Complex.I) =
        ∏ i, Complex.exp ((t i : ℂ) * (x i : ℂ) * Complex.I) := by
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    simp only [Complex.ofReal_mul]
  simp_rw [he]
  let inst : (i : Fin k) → MeasureSpace ℝ := fun i => ⟨gaussianReal 0 (v i)⟩
  have hp := @integral_fintype_prod_eq_prod ℂ _ (Fin k) _ (fun _ => ℝ)
    (fun i (z : ℝ) => Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I)) inst
    (fun i => (inferInstance : SigmaFinite (gaussianReal 0 (v i))))
  have hp' : (∫ x : Fin k → ℝ, ∏ i, Complex.exp ((t i : ℂ) * (x i : ℂ) * Complex.I)
      ∂diagonalGaussian (fun _ => 0) v) =
      ∏ i, ∫ z : ℝ, Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 (v i) := hp
  rw [hp']
  have hg (i : Fin k) :
      (∫ z : ℝ, Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 (v i)) =
        Complex.exp (-((v i : ℝ) : ℂ) * (t i : ℂ) ^ 2 / 2) := by
    simpa only [charFun_apply_real, Complex.ofReal_zero, mul_zero, zero_mul,
      zero_sub, neg_mul, neg_div] using (charFun_gaussianReal (μ := 0) (v := v i) (t i))
  simp_rw [hg]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    ← Finset.sum_neg_distrib, ← Finset.sum_div, neg_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonal_sum_norm_sq {k : ℕ} (v : Fin k → E)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) (t : Fin k → ℝ) :
    ‖∑ i, t i • v i‖ ^ 2 = ∑ i, (t i) ^ 2 * ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · intro j _ hji
    simp only [real_inner_smul_left, real_inner_smul_right, horth i j (Ne.symm hji), mul_zero]
  · simp

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_orthogonal_coordinates {k : ℕ} (v : Fin k → E)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) :
    (euclideanGaussianLaw E).map (fun z i => ⟪v i, z⟫_ℝ) =
      diagonalGaussian (fun _ => 0) (fun i => ⟨‖v i‖ ^ 2, sq_nonneg _⟩) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm
  let f : E → EuclideanSpace ℝ (Fin k) := fun z => e (fun i => ⟪v i, z⟫_ℝ)
  have hf : Continuous f := e.continuous.comp (continuous_pi (fun i => by fun_prop))
  have hcoords : Measurable (fun z : E => fun i => ⟪v i, z⟫_ℝ) := by fun_prop
  have he : (euclideanGaussianLaw E).map f =
      (diagonalGaussian (fun _ => 0) (fun i => ⟨‖v i‖ ^ 2, sq_nonneg _⟩)).map e := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, charFun_apply]
    have hm : StronglyMeasurable (fun z : EuclideanSpace ℝ (Fin k) =>
        Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) :=
      (by fun_prop : Continuous _).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable hf.measurable hm,
      integral_map_of_stronglyMeasurable e.continuous.measurable hm]
    have hinner (z : E) : ⟪f z, t⟫_ℝ = ⟪z, ∑ i, t i • v i⟫_ℝ := by
      simp only [PiLp.inner_apply, f, e, PiLp.continuousLinearEquiv_symm_apply,
        inner_sum, real_inner_smul_right, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm (v i) z]
      rfl
    simp_rw [hinner]
    change charFun (euclideanGaussianLaw E) (∑ i, t i • v i) = _
    rw [euclideanGaussian_characteristic]
    have hscalar (x : Fin k → ℝ) : ⟪e x, t⟫_ℝ = ∑ i, t i * x i := by
      simp only [PiLp.inner_apply, e, PiLp.continuousLinearEquiv_symm_apply,
        RCLike.inner_apply, conj_trivial]
      rfl
    simp_rw [hscalar]
    rw [diagonalGaussian_centered_characteristic]
    congr 1
    rw [← Complex.ofReal_pow, orthogonal_sum_norm_sq v horth]
    simp only [mul_comm]
    rfl
  have hmap := congrArg (fun μ => μ.map e.symm) he
  dsimp only at hmap
  rw [Measure.map_map e.symm.continuous.measurable hf.measurable,
    Measure.map_map e.symm.continuous.measurable e.continuous.measurable] at hmap
  simpa only [Function.comp_def, f, ContinuousLinearEquiv.symm_apply_apply,
    Measure.map_id'] using hmap

end NCBall
