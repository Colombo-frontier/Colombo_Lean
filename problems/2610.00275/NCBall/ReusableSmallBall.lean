import NCBall.HiddenSpectrum
import NCBall.GaussianImageSmallBall

/-! # Small-ball probability after arbitrary adaptive reusable-sample queries -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace NCBall

variable {S F : Type*} [MeasurableSpace S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {H : ℕ}

omit [MeasurableSpace S] [MeasurableSpace F] [BorelSpace F] in
theorem residual_gaussian_smallBall (Q : HandleLatent F H →L[ℝ] HandleLatent F H)
    (hQ : IsResidualProjection Q)
    (hn : 0 < Module.finrank ℝ F)
    (htrace : hiddenVarianceLoss (hiddenEigenbasis hQ) Q < (Module.finrank ℝ F : ℝ) / 16)
    (u : F) :
    (euclideanGaussianLaw (HandleLatent F H)).real
      {z | ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ •
        hiddenBlock F H (Q z) - u‖ ≤ 1 / 16} ≤
      Real.exp (-(Module.finrank ℝ F : ℝ) / 8) := by
  classical
  let n := Module.finrank ℝ F
  let b := hiddenEigenbasis hQ
  let c := (Real.sqrt (n : ℝ))⁻¹
  let T : HandleLatent F H →L[ℝ] F := c • (hiddenBlock F H).comp Q
  let v : Fin n → HandleLatent F H := fun i => c • Q (handleBlock F 0 (b i))
  let A := Finset.univ.filter (fun i => 3 / 4 ≤ hiddenEigenvalues hQ i)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : c ^ 2 = 1 / n := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hn'.le, one_div]
  refine gaussian_linear_image_smallBall b T v ?_ ?_ u A hn' ?_ ?_
  · intro z i
    change ⟪b i, c • hiddenBlock F H (Q z)⟫_ℝ = ⟪c • Q (handleBlock F 0 (b i)), z⟫_ℝ
    rw [real_inner_smul_right, real_inner_smul_left, hQ.2, handleBlock_inner_apply]
    rfl
  · intro i j hij
    have he : ⟪Q (handleBlock F 0 (b i)), Q (handleBlock F 0 (b j))⟫_ℝ = 0 :=
      hidden_eigenrows_orthogonal hQ i j hij
    simp only [v, real_inner_smul_left, real_inner_smul_right,
      he, mul_zero]
  · exact hidden_many_large_variances hQ htrace
  · intro i hi
    have hi' : 3 / 4 ≤ hiddenEigenvalues hQ i := (Finset.mem_filter.mp hi).2
    change 1 / (2 * (n : ℝ)) ≤ ‖c • Q (handleBlock F 0 (b i))‖ ^ 2
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hc, ← hiddenEigenvalues_norm_sq hQ]
    rw [one_div_mul_eq_div]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n) hn').mpr
    nlinarith

theorem reusable_residual_smallBall (p : ReusableQueryPolicy S F H)
    (σ : ℝ) (hσ : 0 < σ) (t : ℕ) (h : LinearHistory S t)
    (hn : 0 < Module.finrank ℝ F)
    (ht : (t : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16) (u : F) :
    (euclideanGaussianLaw (HandleLatent F H)).real
      {z | ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ •
        hiddenBlock F H (linearPosteriorProjection (p.toLinear σ) t h z) - u‖ ≤ 1 / 16} ≤
      Real.exp (-(Module.finrank ℝ F : ℝ) / 8) := by
  have hQ := linearPosteriorProjection_isProjection (p.toLinear σ) t h
  apply residual_gaussian_smallBall _ hQ hn _ u
  have htrace := reusable_posterior_trace_loss (hiddenEigenbasis hQ) p σ hσ t h
  have hdiv : (t : ℝ) / σ ^ 2 < (Module.finrank ℝ F : ℝ) / 16 :=
    (div_lt_iff₀ (sq_pos_of_pos hσ)).mpr (by nlinarith)
  exact htrace.trans_lt hdiv

theorem reusable_posterior_smallBall (p : ReusableQueryPolicy S F H)
    (σ : ℝ) (hσ : 0 < σ) (t : ℕ) (h : LinearHistory S t)
    (hn : 0 < Module.finrank ℝ F)
    (ht : (t : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16) (u : F) :
    (euclideanGaussianLaw (HandleLatent F H)).real
      {z | ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H
        (linearPosteriorMean (p.toLinear σ) t h + linearPosteriorProjection (p.toLinear σ) t h z)
        - u‖ ≤ 1 / 16} ≤ Real.exp (-(Module.finrank ℝ F : ℝ) / 8) := by
  have he (z : HandleLatent F H) :
      (Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H
        (linearPosteriorMean (p.toLinear σ) t h + linearPosteriorProjection (p.toLinear σ) t h z) - u =
      (Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H
        (linearPosteriorProjection (p.toLinear σ) t h z) -
        (u - (Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H
          (linearPosteriorMean (p.toLinear σ) t h)) := by
    rw [map_add, smul_add]
    abel
  simp_rw [he]
  exact reusable_residual_smallBall p σ hσ t h hn ht _

/-- The estimator is any measurable function of the actual recorded history.
Gaussianity, orthogonal coordinates, and the small-ball bound are conclusions,
not assumptions about the conditional distribution. -/
theorem reusable_adaptive_estimation_bound (ν : Measure S) [IsProbabilityMeasure ν]
    (p : ReusableQueryPolicy S F H) (σ : ℝ) (hσ : 0 < σ) (t : ℕ)
    (hn : 0 < Module.finrank ℝ F)
    (ht : (t : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16)
    (u : LinearHistory S t → F) (hu : Measurable u) :
    (ν.prod (euclideanGaussianLaw (HandleLatent F H)))
      {w | ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H w.2 -
        u (linearTranscript (p.toLinear σ) t w)‖ ≤ 1 / 16} ≤
      ENNReal.ofReal (Real.exp (-(Module.finrank ℝ F : ℝ) / 8)) := by
  let B := {w : LinearHistory S t × HandleLatent F H |
    ‖(Real.sqrt (Module.finrank ℝ F : ℝ))⁻¹ • hiddenBlock F H w.2 - u w.1‖ ≤ 1 / 16}
  have hB : MeasurableSet B := by
    apply measurableSet_le
    · exact (((hiddenBlock F H).measurable.comp measurable_snd).const_smul _ |>.sub
        (hu.comp measurable_fst)).norm
    · exact measurable_const
  apply adaptive_gaussian_event_bound ν (p.toLinear σ) t B hB
  intro h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (reusable_posterior_smallBall p σ hσ t h hn ht (u h))

end NCBall
