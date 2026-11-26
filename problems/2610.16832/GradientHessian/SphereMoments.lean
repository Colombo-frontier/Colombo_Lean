import GradientHessian.SphereGaussian
import LowRank.GaussianSquaredMoments

/-!
# Moments of the actual normalized Gaussian sphere law

The Gaussian--sphere product integral proves the even-moment comparison
directly.  Radius/direction independence is not an additional hypothesis.
-/

namespace GradientHessian.SphereMoments

open MeasureTheory ProbabilityTheory Filter
open GradientHessian.GaussianHilbert GradientHessian.SphereGaussian
open scoped InnerProductSpace Matrix
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem invariant_integral_inner_pow (μ : Measure E)
    (hμ : ∀ U : E ≃ₗᵢ[ℝ] E, μ.map U = μ)
    (v w : E) (hvw : ‖v‖ = ‖w‖) (p : ℕ) :
    (∫ x, ⟪v,x⟫_ℝ ^ p ∂μ) = ∫ x, ⟪w,x⟫_ℝ ^ p ∂μ := by
  let U : E ≃ₗᵢ[ℝ] E := (Submodule.span ℝ {v-w})ᗮ.reflection
  have hUv : U v = w := Submodule.reflection_sub hvw
  have hpres : MeasurePreserving U μ μ := ⟨U.continuous.measurable, hμ U⟩
  have h := hpres.integral_comp U.toHomeomorph.measurableEmbedding
    (fun x => ⟪w,x⟫_ℝ ^ p)
  have he : (fun x => ⟪w,U x⟫_ℝ ^ p) = fun x => ⟪v,x⟫_ℝ ^ p := by
    funext x
    rw [← hUv, U.inner_map_map]
  rwa [he] at h

omit [FiniteDimensional ℝ E] in
theorem invariant_moment_radial (μ : Measure E)
    (hμ : ∀ U : E ≃ₗᵢ[ℝ] E, μ.map U = μ)
    (v e : E) (he : ‖e‖ = 1) (p : ℕ) :
    (∫ x, ⟪v,x⟫_ℝ ^ p ∂μ) = ‖v‖ ^ p * ∫ x, ⟪e,x⟫_ℝ ^ p ∂μ := by
  rw [invariant_integral_inner_pow μ hμ v (‖v‖ • e) (by simp [norm_smul, he]) p]
  simp only [real_inner_smul_left, mul_pow, integral_const_mul]

theorem gaussian_norm_even_moment [Nontrivial E] (q : ℕ) :
    (∫ z, ‖z‖ ^ (2*q) ∂euclideanGaussianLaw E) =
      ∏ j ∈ Finset.range q, ((Module.finrank ℝ E : ℝ) + 2*j) := by
  rw [euclideanGaussianLaw, integral_map_of_stronglyMeasurable
    (gaussianSynthesis_continuous E).measurable
    (show StronglyMeasurable (fun z : E => ‖z‖ ^ (2*q)) from
      (show Continuous (fun z : E => ‖z‖ ^ (2*q)) by fun_prop).stronglyMeasurable)]
  simp_rw [pow_mul, gaussianSynthesis_norm_square]
  have hm : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have h := LowRank.gaussian_radial_integral (m := Module.finrank ℝ E)
    Module.finrank_pos (a := (q : ℝ)) (by positivity)
  have he (z : Fin (Module.finrank ℝ E) → ℝ) :
      GaussianSquare.energy z = z ⬝ᵥ z := by
    simp [GaussianSquare.energy, dotProduct, pow_two]
  simp_rw [he]
  rw [show GaussianSquare.gaussianVector (Module.finrank ℝ E) =
    LowRank.iidVectorLaw (Module.finrank ℝ E) 1 from rfl]
  simp only [Real.rpow_natCast] at h
  rw [h]
  simpa only [LowRank.gaussianMomentFormula, Real.rpow_natCast] using
    LowRank.gaussianMomentFormula_nat (m := Module.finrank ℝ E) Module.finrank_pos q

theorem gaussian_norm_even_integrable [Nontrivial E] (q : ℕ) :
    Integrable (fun z : E => ‖z‖ ^ (2*q)) (euclideanGaussianLaw E) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_norm_even_moment]
  apply ne_of_gt
  exact Finset.prod_pos fun j _ => by
    have hm : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
    positivity

theorem sphere_inner_pow_integrable [Nontrivial E] (v : E) (p : ℕ) :
    Integrable (fun x => ⟪v,x⟫_ℝ ^ p) (sphereLaw E) := by
  refine (integrable_const (‖v‖ ^ p)).mono'
    (show Continuous (fun x : E => ⟪v,x⟫_ℝ ^ p) by fun_prop).aestronglyMeasurable ?_
  filter_upwards [sphereLaw_unit (E := E)] with x hx
  have hb : |⟪v,x⟫_ℝ| ≤ ‖v‖ := by simpa [hx] using abs_real_inner_le_norm v x
  simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb p

theorem gaussian_inner_even_integrable [Nontrivial E] (v : E) (q : ℕ) :
    Integrable (fun x => ⟪v,x⟫_ℝ ^ (2*q)) (euclideanGaussianLaw E) := by
  refine ((gaussian_norm_even_integrable (E := E) q).const_mul (‖v‖^(2*q))).mono'
    (show Continuous (fun x : E => ⟪v,x⟫_ℝ ^ (2*q)) by fun_prop).aestronglyMeasurable ?_
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_pow, mul_pow] using
    pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm v x) (2*q)

theorem gaussian_sphere_product_integrable [Nontrivial E] (q : ℕ) :
    Integrable (fun p : E × E => ⟪p.1,p.2⟫_ℝ ^ (2*q))
      ((euclideanGaussianLaw E).prod (sphereLaw E)) := by
  have hb := (gaussian_norm_even_integrable (E := E) q).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : E => (1 : ℝ)) (sphereLaw E))
  simp only [mul_one] at hb
  refine hb.mono' (show Continuous
    (fun p : E × E => ⟪p.1,p.2⟫_ℝ ^ (2*q)) by fun_prop).aestronglyMeasurable ?_
  have hs : ∀ᵐ p : E × E ∂(euclideanGaussianLaw E).prod (sphereLaw E), ‖p.2‖ = 1 :=
    (Measure.ae_prod_iff_ae_ae
      ((isClosed_eq continuous_snd.norm continuous_const).measurableSet :
        MeasurableSet {p : E × E | ‖p.2‖ = 1})).mpr
      (ae_of_all _ fun _ => sphereLaw_unit (E := E))
  filter_upwards [hs] with p hp
  have hi : |⟪p.1,p.2⟫_ℝ| ≤ ‖p.1‖ := by
    simpa [hp] using abs_real_inner_le_norm p.1 p.2
  simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hi (2*q)

/-- Equality of the two orders of the genuine Gaussian--sphere product integral. -/
theorem sphere_gaussian_moment_identity [Nontrivial E] (e : E) (he : ‖e‖ = 1) (q : ℕ) :
    (∫ v, ⟪e,v⟫_ℝ ^ (2*q) ∂sphereLaw E) *
        (∫ z, ‖z‖ ^ (2*q) ∂euclideanGaussianLaw E) =
      ∫ z, ⟪e,z⟫_ℝ ^ (2*q) ∂euclideanGaussianLaw E := by
  have hswap := integral_integral_swap (μ := euclideanGaussianLaw E) (ν := sphereLaw E)
    (f := fun z v : E => ⟪z,v⟫_ℝ ^ (2*q)) (gaussian_sphere_product_integrable (E := E) q)
  change (∫ z, ∫ v, ⟪z,v⟫_ℝ ^ (2*q) ∂sphereLaw E ∂euclideanGaussianLaw E) =
    ∫ v, ∫ z, ⟪z,v⟫_ℝ ^ (2*q) ∂euclideanGaussianLaw E ∂sphereLaw E at hswap
  have hleft : (∫ z, ∫ v, ⟪z,v⟫_ℝ ^ (2*q) ∂sphereLaw E ∂euclideanGaussianLaw E) =
      (∫ v, ⟪e,v⟫_ℝ ^ (2*q) ∂sphereLaw E) *
        (∫ z, ‖z‖ ^ (2*q) ∂euclideanGaussianLaw E) := by
    calc
      _ = ∫ z, ‖z‖^(2*q) * (∫ v, ⟪e,v⟫_ℝ^(2*q) ∂sphereLaw E)
          ∂euclideanGaussianLaw E := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => invariant_moment_radial (sphereLaw E) sphereLaw_isometry z e he (2*q)
      _ = _ := by rw [integral_mul_const]; ring
  rw [hleft] at hswap
  refine hswap.trans ?_
  calc
    _ = ∫ _v : E, (∫ z, ⟪e,z⟫_ℝ ^ (2*q) ∂euclideanGaussianLaw E) ∂sphereLaw E := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_unit (E := E)] with v hv
      rw [show (fun z : E => ⟪z,v⟫_ℝ^(2*q)) = (fun z : E => ⟪v,z⟫_ℝ^(2*q)) by
        funext z; rw [real_inner_comm z v]]
      rw [invariant_moment_radial (euclideanGaussianLaw E) (euclideanGaussian_isometry E) v e he,
        hv, one_pow, one_mul]
    _ = _ := by simp

theorem gaussian_norm_even_moment_lower [Nontrivial E] (q : ℕ) :
    (Module.finrank ℝ E : ℝ)^q ≤ ∫ z, ‖z‖^(2*q) ∂euclideanGaussianLaw E := by
  rw [gaussian_norm_even_moment]
  have hm : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    _ = ∏ _j ∈ Finset.range q, (Module.finrank ℝ E : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => hm) (fun j _ => le_add_of_nonneg_right (by positivity))

theorem sphere_even_moment_le_gaussian [Nontrivial E] (v : E) (q : ℕ) :
    (∫ x, ⟪v,x⟫_ℝ ^ (2*q) ∂sphereLaw E) * (Module.finrank ℝ E : ℝ)^q ≤
      ∫ x, ⟪v,x⟫_ℝ ^ (2*q) ∂euclideanGaussianLaw E := by
  letI : NeZero (Module.finrank ℝ E) := ⟨Module.finrank_pos.ne'⟩
  let e := stdOrthonormalBasis ℝ E (0 : Fin (Module.finrank ℝ E))
  have he : ‖e‖ = 1 := (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one _
  rw [invariant_moment_radial (sphereLaw E) sphereLaw_isometry v e he,
    invariant_moment_radial (euclideanGaussianLaw E) (euclideanGaussian_isometry E) v e he]
  have hs : 0 ≤ ∫ x, ⟪e,x⟫_ℝ ^ (2*q) ∂sphereLaw E :=
    integral_nonneg fun x => by rw [pow_mul]; positivity
  have hb := mul_le_mul_of_nonneg_left (gaussian_norm_even_moment_lower (E := E) q) hs
  rw [sphere_gaussian_moment_identity e he q] at hb
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg v) _)

/-- Every even scalar moment is bounded by that of a Gaussian of variance `1/m`. -/
theorem sphere_even_moment_le_scaled_gaussian [Nontrivial E] (v : E) (q : ℕ) :
    (∫ x, ⟪v,x⟫_ℝ ^ (2*q) ∂sphereLaw E) ≤
      ∫ x, ⟪(Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ • v,x⟫_ℝ ^ (2*q)
        ∂euclideanGaussianLaw E := by
  have hm : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hs : ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹)^(2*q) =
      ((Module.finrank ℝ E : ℝ)^q)⁻¹ := by
    rw [pow_mul, inv_pow, Real.sq_sqrt hm.le, inv_pow]
  simp only [real_inner_smul_left, mul_pow, integral_const_mul, hs]
  have hb := (le_div_iff₀ (pow_pos hm q)).mpr (sphere_even_moment_le_gaussian v q)
  simpa only [div_eq_mul_inv, mul_comm] using hb

end
end GradientHessian.SphereMoments
