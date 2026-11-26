import NCConcave16991.ConditionalHaarCoset
import NCConcave16991.ConditionalHaarColumns
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual conditional Haar completions after fixed finite linear observations

The observed random variable consists of the actual images of a finite family
of prescribed input vectors. Its fibres are the right cosets of their pointwise
stabilizer. Conditional expectation of a continuous test function is proved to
equal integration over an independent normalized Haar element of this closed
stabilizer. This identifies the conditional completion, rather than assuming
its distribution.
-/

open Set MeasureTheory

namespace NCConcave16991.Haar

noncomputable section

variable {k : ℕ} {ι : Type*} [Fintype ι]

theorem action_one (v : EuclideanSpace ℝ (Fin k)) :
    orthogonalLinearIsometryEquiv (1 : OrthogonalGroup k) v = v := by
  simp [orthogonalLinearIsometryEquiv_apply]

def inputStabilizer (v : ι → EuclideanSpace ℝ (Fin k)) : Subgroup (OrthogonalGroup k) where
  carrier := {R | ∀ i, orthogonalLinearIsometryEquiv R (v i) = v i}
  one_mem' := fun i ↦ action_one (v i)
  mul_mem' := by
    intro R S hR hS i
    rw [action_mul, hS i, hR i]
  inv_mem' := by
    intro R hR i
    apply (orthogonalLinearIsometryEquiv R).injective
    rw [← action_mul, mul_inv_cancel, action_one, hR i]

theorem inputStabilizer_closed (v : ι → EuclideanSpace ℝ (Fin k)) :
    IsClosed (inputStabilizer v : Set (OrthogonalGroup k)) := by
  change IsClosed {R | ∀ i, orthogonalLinearIsometryEquiv R (v i) = v i}
  simp_rw [setOf_forall]
  exact isClosed_iInter (fun i ↦ isClosed_eq (continuous_orthogonalLinearIsometryEquiv_apply (v i))
    continuous_const)

def observeInputs (v : ι → EuclideanSpace ℝ (Fin k)) (Q : OrthogonalGroup k) :
    ι → EuclideanSpace ℝ (Fin k) := fun i ↦ orthogonalLinearIsometryEquiv Q (v i)

@[reducible] def inputSigma (v : ι → EuclideanSpace ℝ (Fin k)) : MeasurableSpace (OrthogonalGroup k) :=
  (inferInstance : MeasurableSpace (ι → EuclideanSpace ℝ (Fin k))).comap (observeInputs v)

theorem observeInputs_continuous (v : ι → EuclideanSpace ℝ (Fin k)) :
    Continuous (observeInputs v) := continuous_pi (fun i ↦ continuous_orthogonalLinearIsometryEquiv_apply (v i))

theorem observeInputs_measurable (v : ι → EuclideanSpace ℝ (Fin k)) :
    Measurable (observeInputs v) := (observeInputs_continuous v).measurable

theorem inputSigma_le (v : ι → EuclideanSpace ℝ (Fin k)) :
    inputSigma v ≤ (inferInstance : MeasurableSpace (OrthogonalGroup k)) :=
  (observeInputs_measurable v).comap_le

theorem observeInputs_right_stabilizer (v : ι → EuclideanSpace ℝ (Fin k))
    (Q : OrthogonalGroup k) (R : inputStabilizer v) : observeInputs v (Q * R.val) = observeInputs v Q := by
  funext i
  exact (action_mul Q R.val (v i)).trans (congrArg _ (R.property i))

theorem same_inputs_iff_relative_stabilizer (v : ι → EuclideanSpace ℝ (Fin k))
    (Q R : OrthogonalGroup k) :
    observeInputs v Q = observeInputs v R ↔ Q⁻¹ * R ∈ inputStabilizer v := by
  constructor
  · intro h i
    have hi := congrFun h i
    change orthogonalLinearIsometryEquiv Q (v i) = orthogonalLinearIsometryEquiv R (v i) at hi
    change orthogonalLinearIsometryEquiv (Q⁻¹ * R) (v i) = v i
    rw [action_mul, ← hi, ← action_mul, inv_mul_cancel, action_one]
  · intro h
    funext i
    have hi := congrArg (orthogonalLinearIsometryEquiv Q) (h i)
    rw [← action_mul, mul_inv_cancel_left] at hi
    exact hi.symm

theorem inputSigma_le_cosetSigma (v : ι → EuclideanSpace ℝ (Fin k)) :
    inputSigma v ≤ cosetSigma (inputStabilizer v) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨ht.preimage (observeInputs_measurable v), ?_⟩
  intro R
  ext Q
  simp only [mem_preimage, observeInputs_right_stabilizer]

theorem subgroupAverage_continuous (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) {f : OrthogonalGroup k → ℝ}
    (hf : Continuous f) : Continuous (subgroupAverage H hH f) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  have hc : Continuous (fun a : OrthogonalGroup k × H ↦ f (a.1 * a.2.val)) :=
    hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))
  change Continuous (fun Q : OrthogonalGroup k ↦ ∫ h : H, f (Q * h.val) ∂subgroupHaarLaw H hH)
  have hh := continuous_parametric_integral_of_continuous
    (X := OrthogonalGroup k) (Y := H) (E := ℝ) (μ := subgroupHaarLaw H hH)
    (f := fun Q h ↦ f (Q * h.val)) hc (s := univ) isCompact_univ
  simpa only [Measure.restrict_univ] using hh

/-- A continuous function constant on observation fibres is measurable from
those observations, proved by the compact quotient map onto their range. -/
theorem stronglyMeasurable_input_factor (v : ι → EuclideanSpace ℝ (Fin k))
    {g : OrthogonalGroup k → ℝ} (hg : Continuous g)
    (hconstant : ∀ Q R, observeInputs v Q = observeInputs v R → g Q = g R) :
    StronglyMeasurable[inputSigma v] g := by
  let obs : OrthogonalGroup k → range (observeInputs v) := fun Q ↦ ⟨observeInputs v Q, mem_range_self Q⟩
  have hobs : Continuous obs := (observeInputs_continuous v).subtype_mk _
  have hsurj : Function.Surjective obs := by
    rintro ⟨x,Q,hQ⟩
    exact ⟨Q, Subtype.ext hQ⟩
  have hquot := hobs.isClosedMap.isQuotientMap hobs hsurj
  let pick (x : range (observeInputs v)) : OrthogonalGroup k := Classical.choose x.property
  have hpick (x : range (observeInputs v)) : observeInputs v (pick x) = x.val := Classical.choose_spec x.property
  let G : range (observeInputs v) → ℝ := fun x ↦ g (pick x)
  have hcomp : G ∘ obs = g := by
    funext Q
    exact hconstant _ Q (hpick (obs Q))
  have hG : Continuous G := hquot.continuous_iff.mpr (hcomp ▸ hg)
  have hobsm : Measurable[inputSigma v] obs := by
    apply Measurable.subtype_mk
    exact measurable_iff_comap_le.mpr le_rfl
  have hgm : Measurable[inputSigma v] g := by
    rw [← hcomp]
    exact hG.measurable.comp hobsm
  exact hgm.stronglyMeasurable

theorem completionAverage_inputMeasurable (v : ι → EuclideanSpace ℝ (Fin k))
    {f : OrthogonalGroup k → ℝ} (hf : Continuous f) :
    StronglyMeasurable[inputSigma v]
      (subgroupAverage (inputStabilizer v) (inputStabilizer_closed v) f) := by
  apply stronglyMeasurable_input_factor v (subgroupAverage_continuous _ _ hf)
  intro Q R hQR
  let h : inputStabilizer v := ⟨Q⁻¹ * R, (same_inputs_iff_relative_stabilizer v Q R).mp hQR⟩
  have hinv := subgroupAverage_invariant (inputStabilizer v) (inputStabilizer_closed v) f Q h
  simpa only [h, mul_inv_cancel_left] using hinv.symm

/-- The actual Haar conditional completion law, tested against every continuous
function, after finitely many prescribed forward images have been revealed. -/
theorem conditional_input_completion (v : ι → EuclideanSpace ℝ (Fin k))
    {f : OrthogonalGroup k → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ Q, ‖f Q‖ ≤ M) :
    (haarLaw k)[f | inputSigma v] =ᵐ[haarLaw k]
      subgroupAverage (inputStabilizer v) (inputStabilizer_closed v) f := by
  let H := inputStabilizer v
  let g := subgroupAverage H (inputStabilizer_closed v) f
  have hcos := conditional_subgroupAverage H (inputStabilizer_closed v) hf.stronglyMeasurable hM hb
  have hfi : Integrable f (haarLaw k) := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hgi : Integrable g (haarLaw k) := (integrable_condExp (μ := haarLaw k) (m := cosetSigma H)).congr hcos
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (inputSigma_le v) hfi
    (fun s _ _ ↦ hgi.integrableOn) _ (completionAverage_inputMeasurable v hf).aestronglyMeasurable
  intro s hs hfin
  calc
    _ = ∫ Q in s, (haarLaw k)[f | cosetSigma H] Q ∂haarLaw k :=
      setIntegral_congr_ae (inputSigma_le v s hs) (hcos.symm.mono (fun _ h _ ↦ h))
    _ = _ := setIntegral_condExp (cosetSigma_le H) hfi (inputSigma_le_cosetSigma v s hs)

/-- Compactness supplies the test-function bound automatically. -/
theorem conditional_input_completion_of_continuous (v : ι → EuclideanSpace ℝ (Fin k))
    {f : OrthogonalGroup k → ℝ} (hf : Continuous f) :
    (haarLaw k)[f | inputSigma v] =ᵐ[haarLaw k]
      subgroupAverage (inputStabilizer v) (inputStabilizer_closed v) f := by
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hf.norm.continuousOn
  have hb (Q : OrthogonalGroup k) : ‖f Q‖ ≤ M := hM (mem_image_of_mem _ (mem_univ Q))
  exact conditional_input_completion v hf ((norm_nonneg (f 1)).trans (hb 1)) hb

/-- Coordinate-column observations are the corresponding concrete instance. -/
theorem conditional_column_completion (A : Finset (Fin k))
    {f : OrthogonalGroup k → ℝ} (hf : Continuous f) :
    (haarLaw k)[f | columnSigma A] =ᵐ[haarLaw k]
      subgroupAverage (inputStabilizer (fun j : A ↦ basisVector j.val))
        (inputStabilizer_closed (fun j : A ↦ basisVector j.val)) f :=
  conditional_input_completion_of_continuous (fun j : A ↦ basisVector j.val) hf

end

end NCConcave16991.Haar
