import NCConcave16991.ConditionalHaarSymmetry
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Conditional Haar averaging over a closed stabilizer

For a closed subgroup H of the compact orthogonal group, an actual independent
normalized Haar law on H is constructed. Averaging f(Qh) over that law is then
proved to be the conditional expectation of f given the actual coset data.
Here coset data are represented by their literal saturated Borel events. No
conditional-law specification is used as an assumption.
-/

open Set MeasureTheory

namespace NCConcave16991.Haar

noncomputable section

variable {k : ℕ}

instance orthogonalGroupSecondCountable (k : ℕ) : SecondCountableTopology (OrthogonalGroup k) := by
  letI : SecondCountableTopology (Matrix (Fin k) (Fin k) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

def subgroupHaarFinite (H : Subgroup (OrthogonalGroup k)) (hH : IsClosed (H : Set (OrthogonalGroup k))) :
    FiniteMeasure H := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact ⟨Measure.haar, inferInstance⟩

theorem subgroupHaarFinite_ne_zero (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) : subgroupHaarFinite H hH ≠ 0 := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  intro hz
  have he : (Measure.haar : Measure H) = 0 := by
    simpa [subgroupHaarFinite] using congrArg FiniteMeasure.toMeasure hz
  have hp : (Measure.haar : Measure H) univ ≠ 0 := isOpen_univ.measure_ne_zero _ univ_nonempty
  rw [he] at hp
  exact hp (by simp)

def subgroupHaarLaw (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) : Measure H :=
  (subgroupHaarFinite H hH).normalize

instance subgroupHaarLaw_probability (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) : IsProbabilityMeasure (subgroupHaarLaw H hH) := by
  unfold subgroupHaarLaw
  infer_instance

instance subgroupHaarLaw_leftInvariant (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) : Measure.IsMulLeftInvariant (subgroupHaarLaw H hH) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  rw [subgroupHaarLaw, (subgroupHaarFinite H hH).toMeasure_normalize_eq_of_nonzero
    (subgroupHaarFinite_ne_zero H hH)]
  change Measure.IsMulLeftInvariant ((subgroupHaarFinite H hH).mass⁻¹ • (Measure.haar : Measure H))
  infer_instance

/-- The sigma-field of cosets, represented by the actual saturated Borel sets. -/
@[reducible] def cosetSigma (H : Subgroup (OrthogonalGroup k)) : MeasurableSpace (OrthogonalGroup k) where
  MeasurableSet' s := MeasurableSet s ∧ ∀ h : H, (fun Q : OrthogonalGroup k ↦ Q * h.val) ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ ↦ preimage_empty⟩
  measurableSet_compl := by
    intro s hs
    refine ⟨hs.1.compl, ?_⟩
    intro h
    rw [preimage_compl, hs.2 h]
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion (fun n ↦ (hf n).1), ?_⟩
    intro h
    rw [preimage_iUnion]
    congr 1
    funext n
    exact (hf n).2 h

theorem cosetSigma_le (H : Subgroup (OrthogonalGroup k)) :
    cosetSigma H ≤ (inferInstance : MeasurableSpace (OrthogonalGroup k)) := fun s hs ↦ hs.1

def subgroupAverage (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) (f : OrthogonalGroup k → ℝ) (Q : OrthogonalGroup k) : ℝ :=
  ∫ h : H, f (Q * h.val) ∂subgroupHaarLaw H hH

theorem subgroupAverage_invariant (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) (f : OrthogonalGroup k → ℝ)
    (Q : OrthogonalGroup k) (h0 : H) :
    subgroupAverage H hH f (Q * h0.val) = subgroupAverage H hH f Q := by
  have hh := integral_mul_left_eq_self (μ := subgroupHaarLaw H hH)
    (fun h : H ↦ f (Q * h.val)) h0
  simpa only [subgroupAverage, Subgroup.coe_mul, mul_assoc] using hh

theorem subgroupAverage_stronglyMeasurable (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) {f : OrthogonalGroup k → ℝ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (subgroupAverage H hH f) :=
  (hf.comp_measurable ((continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable)).integral_prod_right'

theorem subgroupAverage_cosetMeasurable (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) {f : OrthogonalGroup k → ℝ}
    (hf : StronglyMeasurable f) : StronglyMeasurable[cosetSigma H] (subgroupAverage H hH f) := by
  apply Measurable.stronglyMeasurable
  intro s hs
  refine ⟨(subgroupAverage_stronglyMeasurable H hH hf).measurable hs, ?_⟩
  intro h
  ext Q
  simp only [mem_preimage, subgroupAverage_invariant]

/-- The actual independent subgroup Haar average is the conditional Haar
law, stated through conditional expectations on the genuine coset sigma-field. -/
theorem conditional_subgroupAverage (H : Subgroup (OrthogonalGroup k))
    (hH : IsClosed (H : Set (OrthogonalGroup k))) {f : OrthogonalGroup k → ℝ}
    (hf : StronglyMeasurable f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ Q, ‖f Q‖ ≤ M) :
    (haarLaw k)[f | cosetSigma H] =ᵐ[haarLaw k] subgroupAverage H hH f := by
  have hmul : Measurable (fun a : OrthogonalGroup k × H ↦ a.1 * a.2.val) :=
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable
  have hFsm := hf.comp_measurable hmul
  have hFint : Integrable (fun a : OrthogonalGroup k × H ↦ f (a.1 * a.2.val))
      ((haarLaw k).prod (subgroupHaarLaw H hH)) := by
    apply (integrable_const M).mono' hFsm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun a ↦ hb _)
  have hfi : Integrable f (haarLaw k) := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hgi : Integrable (subgroupAverage H hH f) (haarLaw k) := hFint.integral_prod_left
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (cosetSigma_le H) hfi
    (fun s _ _ ↦ hgi.integrableOn) _ (subgroupAverage_cosetMeasurable H hH hf).aestronglyMeasurable
  intro s hs hfin
  let F : OrthogonalGroup k × H → ℝ := (Prod.fst ⁻¹' s).indicator (fun a ↦ f (a.1 * a.2.val))
  have hF : Integrable F ((haarLaw k).prod (subgroupHaarLaw H hH)) :=
    hFint.indicator (hs.1.preimage measurable_fst)
  have hpoint (Q : OrthogonalGroup k) :
      s.indicator (subgroupAverage H hH f) Q = ∫ h : H, F (Q,h) ∂subgroupHaarLaw H hH := by
    classical
    by_cases hQ : Q ∈ s <;> simp [F, Set.indicator_apply, hQ, subgroupAverage]
  have hright (h : H) :
      (∫ Q, F (Q,h) ∂haarLaw k) = ∫ Q in s, f Q ∂haarLaw k := by
    have he (Q : OrthogonalGroup k) : F (Q,h) = s.indicator f (Q * h.val) := by
      classical
      have hiff : Q * h.val ∈ s ↔ Q ∈ s := by
        change Q ∈ (fun Q : OrthogonalGroup k ↦ Q * h.val) ⁻¹' s ↔ Q ∈ s
        rw [hs.2 h]
      by_cases hQ : Q ∈ s
      · have hQ' := hiff.mpr hQ
        simp [F, Set.indicator_apply, hQ, hQ']
      · have hQ' : Q * h.val ∉ s := fun hh ↦ hQ (hiff.mp hh)
        simp [F, Set.indicator_apply, hQ, hQ']
    simp_rw [he]
    rw [integral_mul_right_eq_self, integral_indicator hs.1]
  calc
    _ = ∫ Q, s.indicator (subgroupAverage H hH f) Q ∂haarLaw k := (integral_indicator hs.1).symm
    _ = ∫ Q, ∫ h : H, F (Q,h) ∂subgroupHaarLaw H hH ∂haarLaw k := by simp_rw [hpoint]
    _ = ∫ h : H, ∫ Q, F (Q,h) ∂haarLaw k ∂subgroupHaarLaw H hH := integral_integral_swap hF
    _ = _ := by simp_rw [hright]; simp

end

end NCConcave16991.Haar
