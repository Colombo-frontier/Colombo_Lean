import NoisyZO.HardQuantitativeCertificate

/-!
# Finite-dimensional derivative bounds for the radial profile

A smooth compactly supported map has globally bounded iterated derivatives.
The mean value theorem converts the next-derivative bound into a Lipschitz
bound, and a small-distance/large-distance split converts that estimate into
the required fractional Hölder estimate.  Consequently, for every fixed
dimension the explicit unit radial profiles admit common constants over the
finite hypercube.  This does not assert that those constants are independent
of the dimension; that sharper uniformity is the remaining Appendix A input.
-/

open scoped ContDiff Gradient

namespace NoisyZO

noncomputable section

/-- A uniform bound on the next iterated derivative implies a global
Lipschitz bound on the current iterated derivative. -/
theorem norm_iteratedFDeriv_sub_le_of_uniform_next_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (i : ℕ) (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (hbound : ∀ z, ‖iteratedFDeriv ℝ (i + 1) f z‖ ≤ C)
    (x y : E) :
    ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤
      C * ‖x - y‖ := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i f) :=
    hf.differentiable_iteratedFDeriv (by
      exact_mod_cast ENat.natCast_lt_top i)
  have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz ↦ hdiff z)
    (fun z _hz ↦ by
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound z)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [norm_sub_rev y x] using hmv

/-- A bounded, globally Lipschitz map is globally `α`-Hölder for
`0 < α ≤ 1`, with the explicit constant `2C`. -/
theorem norm_iteratedFDeriv_sub_le_two_mul_rpow_of_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (k : ℕ) (alpha C : ℝ)
    (halphaPos : 0 < alpha) (halphaOne : alpha ≤ 1) (hC : 0 ≤ C)
    (hvalue : ∀ z, ‖iteratedFDeriv ℝ k f z‖ ≤ C)
    (hlip : ∀ x y,
      ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤
        C * ‖x - y‖)
    (x y : E) :
    ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤
      (2 * C) * ‖x - y‖ ^ alpha := by
  by_cases hdist : ‖x - y‖ ≤ 1
  · have hpower : ‖x - y‖ ≤ ‖x - y‖ ^ alpha :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) hdist halphaOne
    calc
      ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤
          C * ‖x - y‖ := hlip x y
      _ ≤ C * ‖x - y‖ ^ alpha :=
        mul_le_mul_of_nonneg_left hpower hC
      _ ≤ (2 * C) * ‖x - y‖ ^ alpha := by
        have hp := Real.rpow_nonneg (norm_nonneg (x - y)) alpha
        nlinarith
  · have hpower : 1 ≤ ‖x - y‖ ^ alpha :=
      Real.one_le_rpow (le_of_not_ge hdist) halphaPos.le
    calc
      ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤
          ‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k f y‖ :=
        norm_sub_le _ _
      _ ≤ C + C := add_le_add (hvalue x) (hvalue y)
      _ = 2 * C := by ring
      _ ≤ (2 * C) * ‖x - y‖ ^ alpha := by
        exact le_mul_of_one_le_right (mul_nonneg (by norm_num) hC) hpower

/-- For each fixed hypercube direction, compact support and `C∞` smoothness
produce finite constants for the two unit-profile estimates. -/
theorem exists_unitRadialProfileCertificate
    (o : SmoothnessOrder) {d : ℕ} (s : Hypercube d) :
    ∃ M₂ H : ℝ, UnitRadialProfileCertificate o d s M₂ H := by
  have hsmooth : ContDiff ℝ ∞ (normalizedRadialProfile s) :=
    normalizedRadialProfile_contDiff_infty s
  obtain ⟨C, hC, hbound⟩ :=
    (normalizedRadialProfile_hasCompactSupport s).exists_bound_iteratedFDeriv
      hsmooth (max 2 (o.k + 1))
  refine ⟨C, 2 * C, ?_⟩
  refine
    { M₂_nonneg := hC
      H_nonneg := mul_nonneg (by norm_num) hC
      gradient_lipschitz := ?_
      higher_holder := ?_ }
  · intro x y
    rw [norm_gradient_sub_eq_iteratedFDeriv_one_sub]
    apply norm_iteratedFDeriv_sub_le_of_uniform_next_bound
      (normalizedRadialProfile s) 1 hsmooth C
    intro z
    simpa only [one_add_one_eq_two] using
      hbound 2 (by omega) z
  · intro x y
    apply norm_iteratedFDeriv_sub_le_two_mul_rpow_of_bounds
      (normalizedRadialProfile s) o.k o.alpha C
      o.alpha_pos o.alpha_le_one hC
    · intro z
      exact hbound o.k (by omega) z
    · intro u v
      apply norm_iteratedFDeriv_sub_le_of_uniform_next_bound
        (normalizedRadialProfile s) o.k hsmooth C
      intro z
      exact hbound (o.k + 1) (by omega) z

/-- Enlarge both constants in a unit-profile certificate. -/
theorem UnitRadialProfileCertificate.mono
    {o : SmoothnessOrder} {d : ℕ} {s : Hypercube d}
    {M₂ H M₂' H' : ℝ}
    (cert : UnitRadialProfileCertificate o d s M₂ H)
    (hM₂ : M₂ ≤ M₂') (hH : H ≤ H') :
    UnitRadialProfileCertificate o d s M₂' H' where
  M₂_nonneg := cert.M₂_nonneg.trans hM₂
  H_nonneg := cert.H_nonneg.trans hH
  gradient_lipschitz := by
    intro x y
    exact (cert.gradient_lipschitz x y).trans
      (mul_le_mul_of_nonneg_right hM₂ (norm_nonneg _))
  higher_holder := by
    intro x y
    exact (cert.higher_holder x y).trans
      (mul_le_mul_of_nonneg_right hH
        (Real.rpow_nonneg (norm_nonneg _) _))

/-- In each fixed dimension, one pair of finite constants works for all
Boolean directions, because the hypercube is finite. -/
theorem exists_uniform_unitRadialProfileCertificates
    (o : SmoothnessOrder) (d : ℕ) :
    ∃ M₂ H : ℝ, ∀ s : Hypercube d,
      UnitRadialProfileCertificate o d s M₂ H := by
  choose M₂ H cert using fun s : Hypercube d ↦
    exists_unitRadialProfileCertificate o s
  let M₂' := ∑ s : Hypercube d, M₂ s
  let H' := ∑ s : Hypercube d, H s
  refine ⟨M₂', H', fun s ↦ (cert s).mono ?_ ?_⟩
  · exact Finset.single_le_sum
      (fun t _ht ↦ (cert t).M₂_nonneg) (Finset.mem_univ s)
  · exact Finset.single_le_sum
      (fun t _ht ↦ (cert t).H_nonneg) (Finset.mem_univ s)

/-- In every fixed dimension there is a positive admissible amplitude for
the common (possibly dimension-dependent) profile constants. -/
theorem exists_admissible_amplitude_and_unitProfileCertificates
    (o : SmoothnessOrder) (d : ℕ) :
    ∃ a M₂ H : ℝ,
      0 < a ∧ a ≤ 1 / 4 ∧
      (∀ s : Hypercube d,
        UnitRadialProfileCertificate o d s M₂ H) ∧
      a * M₂ ≤ 1 ∧ a * H ≤ 1 := by
  obtain ⟨M₂, H, cert⟩ :=
    exists_uniform_unitRadialProfileCertificates o d
  have hM₂ : 0 ≤ M₂ := (cert default).M₂_nonneg
  have hH : 0 ≤ H := (cert default).H_nonneg
  let D : ℝ := 4 * (1 + M₂ + H)
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  have hfourD : (4 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith
  have hM₂D : M₂ ≤ D := by
    dsimp [D]
    nlinarith
  have hHD : H ≤ D := by
    dsimp [D]
    nlinarith
  refine ⟨D⁻¹, M₂, H, inv_pos.2 hD, ?_, cert, ?_, ?_⟩
  · rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ hD (by norm_num)).2 hfourD
  · rw [inv_mul_eq_div]
    exact (div_le_one hD).2 hM₂D
  · rw [inv_mul_eq_div]
    exact (div_le_one hD).2 hHD

end

end NoisyZO
