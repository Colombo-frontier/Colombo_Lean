import Mathlib

/-!
# Exact adaptive transcript coupling

This module certifies the abstract transcript and averaging steps in
`source/main.tex`, lines 1028-1038 and 1066-1098. An oracle answer may be an
entire scalar p-jet: the answer type is arbitrary, with no restriction to
values or gradients. The final output may be any function of the transcript
and need not be a query.

The decisive hypothesis is exact agreement of the real and virtual oracle
at the virtual queries. This module DOES NOT prove that the paper's gated
potential supplies this hypothesis, construct a Haar frame, or establish
its conditional spherical concentration bound. Those remain analytic
obligations; the theorems below must not be described as the full oracle
lower bound.
-/

namespace MinimaxAudit.Transcript

universe u v w

/-- A finite history records both the query and the complete answer. -/
abbrev History (Query : Type u) (Answer : Type v) := List (Query × Answer)

/-- An arbitrary deterministic adaptive query rule. Randomized rules can be
handled after fixing their seed; no span or tensor-step restriction occurs. -/
abbrev QueryRule (Query : Type u) (Answer : Type v) :=
  ℕ → History Query Answer → Query

/-- Run an adaptive rule against a possibly round-dependent response map.
The virtual potentials in the paper are round-dependent. -/
def runHistory {Query : Type u} {Answer : Type v}
    (choose : QueryRule Query Answer) (answer : ℕ → Query → Answer) :
    ℕ → History Query Answer
  | 0 => []
  | t + 1 =>
    let h := runHistory choose answer t
    let q := choose t h
    h ++ [(q, answer t q)]

/-- Exactly one query-answer pair is recorded at each round. -/
theorem runHistory_length {Query : Type u} {Answer : Type v}
    (choose : QueryRule Query Answer) (answer : ℕ → Query → Answer)
    (N : ℕ) : (runHistory choose answer N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [runHistory, ih]

/-- Padding later queries preserves the entire earlier transcript. -/
theorem runHistory_take {Query : Type u} {Answer : Type v}
    (choose : QueryRule Query Answer) (answer : ℕ → Query → Answer)
    {k N : ℕ} (hk : k ≤ N) :
    (runHistory choose answer N).take k = runHistory choose answer k := by
  induction N generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    rfl
  | succ N ih =>
    by_cases hkeq : k = N + 1
    · subst k
      simpa only [runHistory_length] using
        (List.take_length (l := runHistory choose answer (N + 1)))
    · have hkle : k ≤ N := by omega
      simp only [runHistory]
      rw [List.take_append_of_le_length (by simpa only [runHistory_length] using hkle)]
      exact ih hkle

/-- An early output can be saved and recovered after arbitrary padding,
without evaluating that output through the oracle. -/
theorem padded_output_eq {Query : Type u} {Answer : Type v} {Output : Type w}
    (choose : QueryRule Query Answer) (answer : ℕ → Query → Answer)
    (finish : History Query Answer → Output) {k N : ℕ} (hk : k ≤ N) :
    finish ((runHistory choose answer N).take k) =
      finish (runHistory choose answer k) := by
  rw [runHistory_take choose answer hk]

/-- Exact oracle agreement at each virtual query forces equality of the full
real and virtual transcripts through the given budget. This is an induction
on the actual adaptive run, not a nonadaptive list-of-queries assumption. -/
theorem histories_eq_of_virtual_agreement
    {Query : Type u} {Answer : Type v}
    (choose : QueryRule Query Answer)
    (real virtual : ℕ → Query → Answer) (N : ℕ)
    (agree : ∀ t < N,
      real t (choose t (runHistory choose virtual t)) =
        virtual t (choose t (runHistory choose virtual t))) :
    ∀ t ≤ N, runHistory choose real t = runHistory choose virtual t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    simp only [runHistory, hprev, agree t (by omega)]

/-- Query equality follows from transcript equality, even when the query
rule performs arbitrary computation on every previous complete answer. -/
theorem queries_eq_of_virtual_agreement
    {Query : Type u} {Answer : Type v}
    (choose : QueryRule Query Answer)
    (real virtual : ℕ → Query → Answer) (N : ℕ)
    (agree : ∀ t < N,
      real t (choose t (runHistory choose virtual t)) =
        virtual t (choose t (runHistory choose virtual t)))
    (t : ℕ) (ht : t ≤ N) :
    choose t (runHistory choose real t) =
      choose t (runHistory choose virtual t) := by
  rw [histories_eq_of_virtual_agreement choose real virtual N agree t ht]

/-- An arbitrary, possibly unqueried output is identical in the two runs.
There is no additional output-oracle call in this statement. -/
theorem output_eq_of_virtual_agreement
    {Query : Type u} {Answer : Type v} {Output : Type w}
    (choose : QueryRule Query Answer)
    (finish : History Query Answer → Output)
    (real virtual : ℕ → Query → Answer) (N : ℕ)
    (agree : ∀ t < N,
      real t (choose t (runHistory choose virtual t)) =
        virtual t (choose t (runHistory choose virtual t))) :
    finish (runHistory choose real N) =
      finish (runHistory choose virtual N) := by
  rw [histories_eq_of_virtual_agreement choose real virtual N agree N le_rfl]

/-- Any terminal geometric predicate proved for the virtual output transfers
to the real output on an exact-coupling event. -/
theorem terminal_property_of_virtual_agreement
    {Query : Type u} {Answer : Type v} {Output : Type w}
    (choose : QueryRule Query Answer)
    (finish : History Query Answer → Output)
    (real virtual : ℕ → Query → Answer) (N : ℕ)
    (agree : ∀ t < N,
      real t (choose t (runHistory choose virtual t)) =
        virtual t (choose t (runHistory choose virtual t)))
    (P : Output → Prop)
    (hvirtual : P (finish (runHistory choose virtual N))) :
    P (finish (runHistory choose real N)) := by
  rwa [output_eq_of_virtual_agreement choose finish real virtual N agree]

open MeasureTheory
open scoped ENNReal

/-- The finite union bound needs no independence among future frame columns
or among bad events. Conditional tail bounds needed to instantiate `hbound`
are not proved here. -/
theorem finite_failure_union_bound
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Finset ι) (bad : ι → Set Ω)
    (bound : ι → ℝ≥0∞)
    (hbound : ∀ i ∈ I, μ (bad i) ≤ bound i) :
    μ (⋃ i ∈ I, bad i) ≤ ∑ i ∈ I, bound i := by
  exact (measure_biUnion_finset_le I bad).trans (Finset.sum_le_sum hbound)

/-- Complementing the finite union bound gives the good-event probability
without any independence assumption. -/
theorem finite_good_event_probability
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ι) (bad : ι → Set Ω)
    (hbad : ∀ i ∈ I, MeasurableSet (bad i))
    (bound : ι → ℝ≥0∞)
    (hbound : ∀ i ∈ I, μ (bad i) ≤ bound i) :
    1 - (∑ i ∈ I, bound i) ≤ μ (⋃ i ∈ I, bad i)ᶜ := by
  have hmeas : MeasurableSet (⋃ i ∈ I, bad i) :=
    MeasurableSet.biUnion I.countable_toSet hbad
  rw [prob_compl_eq_one_sub hmeas]
  exact tsub_le_tsub_left (finite_failure_union_bound μ I bad bound hbound) 1

/-- Extract one fixed frame from an established average seed-failure
probability. Integrability and the joint-to-iterated expectation identity
are explicit separate obligations. -/
theorem exists_fixed_frame_of_average_failure
    {Frame : Type u} [MeasurableSpace Frame]
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (failure : Frame → ℝ) (hf : Integrable failure μ)
    (threshold : ℝ)
    (haverage : threshold ≤ ∫ frame, failure frame ∂μ) :
    ∃ frame, threshold ≤ failure frame := by
  obtain ⟨frame, hframe⟩ := exists_integral_le hf
  exact ⟨frame, haverage.trans hframe⟩

/-- A measurable joint failure event on independent frame and seed spaces
admits a single fixed frame whose seed-failure probability is at least the
joint lower bound. This includes the product-measure / iterated-probability
identity, rather than assuming that identity as a separate premise. -/
theorem exists_fixed_frame_of_joint_failure
    {Frame : Type u} {Seed : Type v}
    [MeasurableSpace Frame] [MeasurableSpace Seed]
    (μ : Measure Frame) (ν : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (bad : Set (Frame × Seed)) (hbad : MeasurableSet bad)
    (threshold : ℝ≥0∞) (hjoint : threshold ≤ (μ.prod ν) bad) :
    ∃ frame, threshold ≤ ν {seed | (frame, seed) ∈ bad} := by
  have hprod : (μ.prod ν) bad =
      ∫⁻ frame, ν (Prod.mk frame ⁻¹' bad) ∂μ :=
    Measure.prod_apply hbad
  have hfinite : (∫⁻ frame, ν (Prod.mk frame ⁻¹' bad) ∂μ) ≠ ∞ := by
    rw [← hprod]
    exact measure_ne_top (μ.prod ν) bad
  obtain ⟨frame, hframe⟩ := exists_lintegral_le hfinite
  refine ⟨frame, ?_⟩
  change threshold ≤ ν (Prod.mk frame ⁻¹' bad)
  exact (hjoint.trans_eq hprod).trans hframe

/-- Full abstract final step for the randomized proof: exact transcript
coupling on a joint good event transfers a terminal obstruction and yields
one frame fixed independently of the realized seed. Neither the gated
potential nor its Haar good-event estimate is assumed to be constructed by
this theorem; these are the explicit premises `agree`, `hvirtual`, and
`hgood` that a source-specific proof must discharge. -/
theorem fixed_frame_of_coupled_obstruction
    {Frame Seed Query Answer Output : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed]
    (μ : Measure Frame) (ν : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (choose : Frame → Seed → QueryRule Query Answer)
    (finish : Frame → Seed → History Query Answer → Output)
    (real virtual : Frame → ℕ → Query → Answer) (N : ℕ)
    (P : Frame → Output → Prop)
    (good : Set (Frame × Seed))
    (threshold : ℝ≥0∞) (hgood : threshold ≤ (μ.prod ν) good)
    (agree : ∀ w ∈ good, ∀ t < N,
      real w.1 t (choose w.1 w.2 t
        (runHistory (choose w.1 w.2) (virtual w.1) t)) =
      virtual w.1 t (choose w.1 w.2 t
        (runHistory (choose w.1 w.2) (virtual w.1) t)))
    (hvirtual : ∀ w ∈ good,
      P w.1 (finish w.1 w.2
        (runHistory (choose w.1 w.2) (virtual w.1) N)))
    (hbad : MeasurableSet {w : Frame × Seed |
      P w.1 (finish w.1 w.2
        (runHistory (choose w.1 w.2) (real w.1) N))}) :
    ∃ frame, threshold ≤ ν {seed |
      P frame (finish frame seed
        (runHistory (choose frame seed) (real frame) N))} := by
  apply exists_fixed_frame_of_joint_failure μ ν _ hbad threshold
  refine hgood.trans (measure_mono ?_)
  intro w hw
  exact terminal_property_of_virtual_agreement
    (choose w.1 w.2) (finish w.1 w.2) (real w.1) (virtual w.1)
    N (agree w hw) (P w.1) (hvirtual w hw)

end MinimaxAudit.Transcript
