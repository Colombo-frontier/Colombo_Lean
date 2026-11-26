import GradientHessian.ForkProbability
import GradientHessian.UnmarkedReadout

/-!
# Integrating the concrete source fork geometry

The test family may be any measurable function of all displayed inputs.  The
conclusion is the lower-bound side of the fork argument; chronological oracle
admissibility is needed only for its separate posterior upper bound.
-/

namespace GradientHessian.ForkSourceExpectation

open Matrix MeasureTheory LowRank
open GradientHessian.ForkColumns GradientHessian.ForkTrace
open GradientHessian.ForkProbability GradientHessian.SphereColumnNorm
open GradientHessian.MatrixGoodSpectrum
open scoped InnerProductSpace ENNReal BigOperators
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def sourceCount {d n r s : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (γ : ℝ) (p : Ω × (Fin r → EuclideanSpace ℝ (Fin r))) : ℝ :=
  ((sourceHits P J (X p.1) fallback (embeddedMarks B p.2) (tests p) γ).card : ℝ)

def sourceOverlap {d n r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (p : Ω × (Fin r → EuclideanSpace ℝ (Fin r))) : ℝ :=
  (branchProjector P (tests p)*leftKernelProjector (X p.1)).trace

theorem sourceCount_measurable {d n r s : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ) (hX : Measurable X)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (ht : Measurable tests) (γ : ℝ) : Measurable (sourceCount J P B fallback X tests γ) := by
  classical
  let H := fun i : Fin r => {p : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) |
    ∃ j, γ < |⟪UnmarkedReadout.sourceOutput J P (X p.1) B fallback (p.2 i), tests p i j⟫_ℝ|}
  have hH (i : Fin r) : MeasurableSet (H i) := by
    dsimp only [H]
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro j
    have ha := UnmarkedReadout.sourceOutput_measurable_comp J P B fallback
      (fun p : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) => X p.1)
      (fun p => p.2 i) (hX.comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd)
    have hy := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp ht)
    exact measurableSet_lt measurable_const (ha.inner hy).abs
  have he (p : Ω × (Fin r → EuclideanSpace ℝ (Fin r))) :
      sourceCount J P B fallback X tests γ p =
        ∑ i, (H i).indicator (fun _ => (1:ℝ)) p := by
    unfold sourceCount sourceHits
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : p ∈ H i
    · simp only [Set.indicator_of_mem h]
      have h' : ∃ j, γ < |⟪(WithLp.equiv 2 (Fin d → ℝ)).symm
          (ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P (sourceMatrix P J (X p.1))
            fallback ⇑(embeddedMarks B p.2 i)), tests p i j⟫_ℝ| := h
      simp only [if_pos h', Nat.cast_one]
    · simp only [Set.indicator_of_not_mem h]
      have h' : ¬∃ j, γ < |⟪(WithLp.equiv 2 (Fin d → ℝ)).symm
          (ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P (sourceMatrix P J (X p.1))
            fallback ⇑(embeddedMarks B p.2 i)), tests p i j⟫_ℝ| := h
      simp only [if_neg h', Nat.cast_zero]
  change Measurable (fun p => sourceCount J P B fallback X tests γ p)
  simp_rw [he]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hH i))

omit [MeasurableSpace Ω] in
theorem sourceCount_bounds {d n r s : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (γ : ℝ) (p : Ω × (Fin r → EuclideanSpace ℝ (Fin r))) :
    0 ≤ sourceCount J P B fallback X tests γ p ∧ sourceCount J P B fallback X tests γ p ≤ r := by
  classical
  refine ⟨Nat.cast_nonneg _, ?_⟩
  change ((Finset.univ.filter _).card : ℝ) ≤ (r:ℝ)
  exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin r))

theorem sourceOverlap_measurable {d n r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ) (hX : Measurable X)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (ht : Measurable tests) : Measurable (sourceOverlap P X tests) := by
  have hflat : Measurable (fun p => flattenedTests (tests p)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    unfold flattenedTests columnMatrix
    fun_prop
  have hR := (measurable_testProjector P).comp hflat
  have hK : Measurable (fun p : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) =>
      leftKernelProjector (X p.1)) :=
    (measurable_leftKernelProjector (m := Fin d) (n := Fin n)).comp
      (hX.comp measurable_fst)
  unfold sourceOverlap branchProjector
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

omit [MeasurableSpace Ω] in
theorem sourceOverlap_bounds {d n r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (p : Ω × (Fin r → EuclideanSpace ℝ (Fin r))) :
    0 ≤ sourceOverlap P X tests p ∧ sourceOverlap P X tests p ≤ (r*s:ℕ) := by
  exact ⟨projector_overlap_nonneg (testProjector_isProjector _ _)
    (leftKernelProjector_isProjector _),
    (projector_overlap_le (testProjector_isProjector _ _) (leftKernelProjector_isProjector _)).trans
      (testProjector_trace_le _ _)⟩

/-- Actual source-event hit counts satisfy the integral estimate, with an
explicit exponential exceptional cost. No trace implication, integrability,
spherical-column bound, or matrix-event probability is assumed as a premise. -/
theorem source_mean_hitCount_le {d n r s : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hr : 0 < r)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {J : ℕ} (hJ : 4 ≤ J) (B : Matrix (Fin d) (Fin r) ℝ)
    (hB : Bᵀ*B = 1) (hPB : P*B = B) (fallback : Fin d → ℝ)
    (X : Ω → Matrix (Fin d) (Fin n) ℝ) (hX : Measurable X)
    (tests : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) → Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (ht : Measurable tests) (hnorm : ∀ p i j, ‖tests p i j‖ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) (hδ : 5*ReadoutFilter.delta ≤ γ/4) :
    (∫ p, {p : Ω × (Fin r → EuclideanSpace ℝ (Fin r)) |
        X p.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J}.indicator
      (sourceCount J P B fallback X tests γ) p
      ∂μ.prod (columnLaw (EuclideanSpace ℝ (Fin r)) r)) ≤
      (256/γ^2)*(∫ p, sourceOverlap P X tests p
        ∂μ.prod (columnLaw (EuclideanSpace ℝ (Fin r)) r)) +
      (r:ℝ)*Real.exp (-Real.log (3/2:ℝ)*(r:ℝ)) := by
  let ρ := columnLaw (EuclideanSpace ℝ (Fin r)) r
  let E : Set (Ω × (Fin r → EuclideanSpace ℝ (Fin r))) :=
    {p | X p.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J}
  let bad : Set (Fin r → EuclideanSpace ℝ (Fin r)) :=
    {z | 4 < ‖matrixEuclideanMap (columnMatrix z)‖}
  have hE : MeasurableSet E :=
    (MatrixKernelConcentration.measurableSet_sourceGoodEvent P J).preimage (hX.comp measurable_fst)
  have hbad : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    exact ((continuous_matrixEuclideanMap r r).comp
      (show Continuous (columnMatrix (D := r) (n := r)) by
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (EuclideanSpace.proj i).continuous.comp (continuous_apply j))).measurable.norm
  have hHi : Integrable (sourceCount J P B fallback X tests γ) (μ.prod ρ) := by
    apply (integrable_const (r:ℝ)).mono' (sourceCount_measurable J P B fallback X hX tests ht γ).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceCount_bounds J P B fallback X tests γ p).1]
    exact (sourceCount_bounds J P B fallback X tests γ p).2
  have hTi : Integrable (sourceOverlap P X tests) (μ.prod ρ) := by
    apply (integrable_const ((r*s:ℕ):ℝ)).mono' (sourceOverlap_measurable P X hX tests ht).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceOverlap_bounds P X tests p).1]
    exact (sourceOverlap_bounds P X tests p).2
  have htrace : ∀ᵐ p ∂μ.prod ρ, p ∈ E → p ∉ Set.univ ×ˢ bad →
      γ^2*sourceCount J P B fallback X tests γ p/256 ≤ sourceOverlap P X tests p := by
    have hunit : ∀ᵐ p ∂μ.prod ρ, ∀ i, ‖embeddedMarks B p.2 i‖ = 1 :=
      Measure.quasiMeasurePreserving_snd.ae (embeddedMarks_unit hr B hB)
    filter_upwards [hunit] with p hp
    intro he hb
    have hw : ‖matrixEuclideanMap (columnMatrix (embeddedMarks B p.2))‖ ≤ 4 :=
      (embeddedMarks_opNorm_le B hB p.2).trans (le_of_not_gt (by simpa [bad] using hb))
    exact source_fork_trace hP hJ he fallback (embeddedMarks B p.2) hp
      (embeddedMarks_range P B hPB p.2) hw (tests p) (hnorm p) hγ.le hδ
  have hi := integral_event_count_le (μ.prod ρ) hE (MeasurableSet.univ.prod hbad)
    (sourceCount J P B fallback X tests γ) (sourceOverlap P X tests) hHi hTi
    (Nat.cast_nonneg r) hγ
    (Filter.Eventually.of_forall (fun p => (sourceCount_bounds J P B fallback X tests γ p).2))
    (Filter.Eventually.of_forall (fun p => (sourceOverlap_bounds P X tests p).1)) htrace
  have hbprob : (μ.prod ρ).real (Set.univ ×ˢ bad) ≤
      Real.exp (-Real.log (3/2:ℝ)*(r:ℝ)) := by
    have heq : (μ.prod ρ).real (Set.univ ×ˢ bad) = ρ.real bad := by
      simp [measureReal_def, Measure.prod_prod]
    rw [heq]
    exact manuscript_column_sphere_tail hr
  exact hi.trans (add_le_add_left (mul_le_mul_of_nonneg_left hbprob (Nat.cast_nonneg r)) _)

end
end GradientHessian.ForkSourceExpectation
