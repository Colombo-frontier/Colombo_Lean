import NCConcave16991.ConditionalHaarTail

/-!
# Actual Haar tail bounds at observable finite stopping states

A revelation state is allowed to be random. Its fibre must be determined by
the columns that this state reveals. A finite partition then combines the
actual conditional Haar bounds without a factor for the number of possible
states. These are structural measurability conditions on a stopping rule,
not assumed conditional distributions.
-/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.Haar

noncomputable section

theorem stopped_observed_probe_tail_weighted {k S : ℕ}
    (state : OrthogonalGroup k → Fin S) (A : Fin S → Finset (Fin k))
    (hstate : ∀ s, MeasurableSet[columnSigma (A s)] {Q | state Q = s})
    (a : Fin S → OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : ∀ s, StronglyMeasurable[columnSigma (A s)] (a s))
    (C : Fin S → ℝ) (hC : ∀ s, 0 ≤ C s) (hb : ∀ s Q, ‖a s Q‖ ≤ C s)
    (j : Fin S → Fin k) (hj : ∀ s, j s ∉ A s) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | r ≤ |⟪a (state Q) Q,
      orthogonalLinearIsometryEquiv Q (basisVector (j (state Q)))⟫_ℝ|} ≤
      ∑ s, (haarLaw k).real {Q | state Q = s} *
        (C s ^ 2 / (((A s)ᶜ.card : ℝ) * r ^ 2)) := by
  have he : {Q : OrthogonalGroup k | r ≤ |⟪a (state Q) Q,
        orthogonalLinearIsometryEquiv Q (basisVector (j (state Q)))⟫_ℝ|} =
      ⋃ s : Fin S, {Q | state Q = s} ∩
        {Q | r ≤ |⟪a s Q, orthogonalLinearIsometryEquiv Q (basisVector (j s))⟫_ℝ|} := by
    ext Q
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨state Q, rfl, h⟩
    · rintro ⟨s, hs, h⟩
      simpa only [hs] using h
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun s _ ↦ observed_inner_tail_on_event (A s) (a s) (ha s)
      (hC s) (hb s) (j s) (hj s) hr (hstate s)))

/-- The number of possible stopping states does not enter the bound. -/
theorem stopped_observed_probe_tail {k S d : ℕ} (hd : 0 < d)
    (state : OrthogonalGroup k → Fin S) (A : Fin S → Finset (Fin k))
    (hstate : ∀ s, MeasurableSet[columnSigma (A s)] {Q | state Q = s})
    (hdim : ∀ s, d ≤ (A s)ᶜ.card)
    (a : Fin S → OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (ha : ∀ s, StronglyMeasurable[columnSigma (A s)] (a s))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ s Q, ‖a s Q‖ ≤ C)
    (j : Fin S → Fin k) (hj : ∀ s, j s ∉ A s) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | r ≤ |⟪a (state Q) Q,
      orthogonalLinearIsometryEquiv Q (basisVector (j (state Q)))⟫_ℝ|} ≤
      C ^ 2 / ((d : ℝ) * r ^ 2) := by
  have hsum : (∑ s : Fin S, (haarLaw k).real {Q | state Q = s}) = 1 := by
    have hmeas (s : Fin S) : MeasurableSet (state ⁻¹' {s}) := by
      change MeasurableSet {Q | state Q = s}
      exact columnSigma_le (A s) _ (hstate s)
    have hs := sum_measureReal_preimage_singleton (μ := haarLaw k) Finset.univ
      (f := state) (fun s _ ↦ hmeas s)
    have hs' : (∑ s : Fin S, (haarLaw k).real (state ⁻¹' {s})) = 1 := by simpa using hs
    simpa only [Set.preimage, mem_singleton_iff] using hs'
  have hbd (s : Fin S) : C ^ 2 / (((A s)ᶜ.card : ℝ) * r ^ 2) ≤
      C ^ 2 / ((d : ℝ) * r ^ 2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg C) (mul_pos (by exact_mod_cast hd) (sq_pos_of_pos hr))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdim s) (sq_nonneg r)
  calc
    _ ≤ ∑ s, (haarLaw k).real {Q | state Q = s} *
        (C ^ 2 / (((A s)ᶜ.card : ℝ) * r ^ 2)) :=
      stopped_observed_probe_tail_weighted state A hstate a ha (fun _ ↦ C)
        (fun _ ↦ hC) hb j hj hr
    _ ≤ ∑ s, (haarLaw k).real {Q | state Q = s} * (C ^ 2 / ((d : ℝ) * r ^ 2)) :=
      Finset.sum_le_sum (fun s _ ↦ mul_le_mul_of_nonneg_left (hbd s) measureReal_nonneg)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end

end NCConcave16991.Haar
