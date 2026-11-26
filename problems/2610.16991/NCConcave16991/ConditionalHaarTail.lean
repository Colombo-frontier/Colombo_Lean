import NCConcave16991.ConditionalHaarVectorProbe
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Actual conditional Haar tails for observation-dependent probes

The probing vector is a bounded measurable function of the actual revealed
columns. Conditional Chebyshev and its integrated consequence follow from the
proved conditional second moment, with no independence or isotropy premise.
-/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar

noncomputable section

theorem observed_inner_measurable {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) (j : Fin k) :
    Measurable (fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ) :=
  ((ha.mono (columnSigma_le A)).measurable).inner
    (continuous_orthogonalLinearIsometryEquiv_apply (basisVector j)).measurable

theorem observed_inner_norm_le {k : ℕ}
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k)) {C : ℝ}
    (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) (Q : OrthogonalGroup k) :
    ‖⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ‖ ≤ C := by
  have hnorm : ‖orthogonalLinearIsometryEquiv Q (basisVector j)‖ = 1 := by
    rw [(orthogonalLinearIsometryEquiv Q).norm_map]
    simp [basisVector]
  apply (norm_inner_le_norm _ _).trans
  rw [hnorm, mul_one]
  exact hb Q

theorem observed_inner_square_integrable {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) :
    Integrable (fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ ^ 2) (haarLaw k) := by
  apply (integrable_const (C ^ 2)).mono' ((observed_inner_measurable A a ha j).pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro Q
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) (observed_inner_norm_le a hb j Q) 2

/-- The actual conditional bad-event probability for a history-dependent probe. -/
theorem conditional_inner_tail {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ Q ∂haarLaw k,
      ((haarLaw k)[({Q | r ≤ |⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ|}.indicator
        (fun _ ↦ (1:ℝ))) | columnSigma A]) Q ≤ C ^ 2 / ((Aᶜ.card : ℝ) * r ^ 2) := by
  let z : OrthogonalGroup k → ℝ := fun Q ↦ ⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ
  let s : Set (OrthogonalGroup k) := {Q | r ≤ |z Q|}
  have hz : Measurable z := observed_inner_measurable A a ha j
  have hs : MeasurableSet s := measurableSet_le measurable_const (continuous_abs.measurable.comp hz)
  have hz2 : Integrable (fun Q ↦ z Q ^ 2) (haarLaw k) := observed_inner_square_integrable A a ha hb j
  have hle : s.indicator (fun _ ↦ (1:ℝ)) ≤ᵐ[haarLaw k] fun Q ↦ (r ^ 2)⁻¹ * z Q ^ 2 := by
    apply Filter.Eventually.of_forall
    intro Q
    by_cases hQ : Q ∈ s
    · rw [indicator_of_mem hQ]
      have hsq : r ^ 2 ≤ z Q ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ hr.le hQ 2
      have hh := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg r))
      simpa only [inv_mul_cancel₀ (sq_pos_of_pos hr).ne'] using hh
    · rw [indicator_of_notMem hQ]
      exact mul_nonneg (inv_nonneg.mpr (sq_nonneg r)) (sq_nonneg _)
  have hm := condExp_mono (m := columnSigma A) ((integrable_const (1:ℝ)).indicator hs)
    (hz2.const_mul (r ^ 2)⁻¹) hle
  have hscale := condExp_smul (μ := haarLaw k) (r ^ 2)⁻¹ (fun Q ↦ z Q ^ 2) (columnSigma A)
  have hsecond := conditional_inner_second_moment_bound A a ha hC hb j hj
  filter_upwards [hm, hscale, hsecond] with Q hQ hScale hSecond
  change ((haarLaw k)[s.indicator (fun _ ↦ (1:ℝ)) | columnSigma A]) Q ≤ _
  calc
    _ ≤ ((haarLaw k)[(fun Q ↦ (r ^ 2)⁻¹ * z Q ^ 2) | columnSigma A]) Q := hQ
    _ = (r ^ 2)⁻¹ * ((haarLaw k)[(fun Q ↦ z Q ^ 2) | columnSigma A]) Q := hScale
    _ ≤ (r ^ 2)⁻¹ * (C ^ 2 / (Aᶜ.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hSecond (inv_nonneg.mpr (sq_nonneg r))
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Integrating the conditional tail permits observation-dependent query
vectors in the resulting probability estimate. -/
theorem observed_inner_tail {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | r ≤ |⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ|} ≤
      C ^ 2 / ((Aᶜ.card : ℝ) * r ^ 2) := by
  have htail := conditional_inner_tail A a ha hC hb j hj hr
  have hm := integral_mono_ae integrable_condExp
    (integrable_const (C ^ 2 / ((Aᶜ.card : ℝ) * r ^ 2))) htail
  rw [integral_condExp (columnSigma_le A)] at hm
  have hs : MeasurableSet {Q | r ≤ |⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (observed_inner_measurable A a ha j))
  rw [integral_indicator_const (1 : ℝ) hs] at hm
  simpa using hm

/-- The probability estimate can be restricted to any event known from the
revealed images. This is the finite-partition ingredient for random stopping
sets of revealed coordinates. -/
theorem observed_inner_tail_on_event {k : ℕ} (A : Finset (Fin k))
    (a : OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : StronglyMeasurable[columnSigma A] a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Q, ‖a Q‖ ≤ C) (j : Fin k) (hj : j ∉ A) {r : ℝ} (hr : 0 < r)
    {s : Set (OrthogonalGroup k)} (hs : MeasurableSet[columnSigma A] s) :
    (haarLaw k).real (s ∩ {Q | r ≤ |⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ|}) ≤
      (haarLaw k).real s * (C ^ 2 / ((Aᶜ.card : ℝ) * r ^ 2)) := by
  let bad : Set (OrthogonalGroup k) :=
    {Q | r ≤ |⟪a Q, orthogonalLinearIsometryEquiv Q (basisVector j)⟫_ℝ|}
  have hbad : MeasurableSet bad :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (observed_inner_measurable A a ha j))
  have hint : Integrable (bad.indicator (fun _ ↦ (1:ℝ))) (haarLaw k) :=
    (integrable_const (1:ℝ)).indicator hbad
  have hm := integral_mono_ae (μ := (haarLaw k).restrict s) integrable_condExp.integrableOn
    (integrable_const (C ^ 2 / ((Aᶜ.card : ℝ) * r ^ 2)))
    (ae_restrict_of_ae (conditional_inner_tail A a ha hC hb j hj hr))
  rw [setIntegral_condExp (columnSigma_le A) hint hs, setIntegral_indicator hbad,
    setIntegral_const, setIntegral_const] at hm
  simpa only [smul_eq_mul, mul_one] using hm

/-- A finite collection of probes may each depend on their own prescribed
revealed columns. The actual Haar union bound sums their residual dimensions. -/
theorem finite_observed_probe_union_tail {k N : ℕ}
    (A : Fin N → Finset (Fin k))
    (a : Fin N → OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : ∀ t, StronglyMeasurable[columnSigma (A t)] (a t))
    (C : Fin N → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t Q, ‖a t Q‖ ≤ C t)
    (j : Fin N → Fin k) (hj : ∀ t, j t ∉ A t) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | ∃ t, r ≤ |⟪a t Q, orthogonalLinearIsometryEquiv Q (basisVector (j t))⟫_ℝ|} ≤
      ∑ t, C t ^ 2 / (((A t)ᶜ.card : ℝ) * r ^ 2) := by
  have he : {Q : OrthogonalGroup k | ∃ t, r ≤ |⟪a t Q, orthogonalLinearIsometryEquiv Q (basisVector (j t))⟫_ℝ|} =
      ⋃ t : Fin N, {Q | r ≤ |⟪a t Q, orthogonalLinearIsometryEquiv Q (basisVector (j t))⟫_ℝ|} := by
    ext Q
    simp
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun t _ ↦ observed_inner_tail (A t) (a t) (ha t) (hC t) (hb t) (j t) (hj t) hr))

end

end NCConcave16991.Haar
