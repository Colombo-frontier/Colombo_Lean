import HeavyTail.RejectionIdealExecution

/-! Full distribution coupling for manuscript lines 685--693. The first
marginal is the actual raw-capped policy and the second is the genuine ideal
accepted process. Their outputs disagree with probability at most 2^(-8n).
Consequently ideal concentration transfers with an additive raw-cap failure
term, without conditioning the ideal law on successful completion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace HeavyTail

theorem completion_coupling_disagreement {H O : Type*} [MeasurableSpace H]
    [MeasurableSpace O] (P : Measure H) [IsProbabilityMeasure P]
    (C : Kernel H O) [IsMarkovKernel C] (f : H → O) (hf : Measurable f)
    {A : Set H} (hA : MeasurableSet A) (hdone : ∀ h, h ∉ A → C h = Measure.dirac (f h))
    (hdiag : MeasurableSet {z : O × O | z.1 ≠ z.2}) :
    ((P.compProd C).map (fun z => (f z.1, z.2))) {z | z.1 ≠ z.2} ≤ P A := by
  have hm : Measurable (fun z : H × O => (f z.1, z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hm hdiag, Measure.compProd_apply (hdiag.preimage hm)]
  calc
    _ ≤ ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) h ∂P := by
      apply lintegral_mono
      intro h
      by_cases hh : h ∈ A
      · simp only [Set.indicator_of_mem hh, Set.mem_preimage, Set.mem_setOf_eq]
        exact prob_le_one
      · rw [Set.indicator_of_not_mem hh]
        change C h {y | f h ≠ y} ≤ 0
        rw [hdone h hh]
        have hset : MeasurableSet {y : O | f h ≠ y} :=
          hdiag.preimage (measurable_const.prodMk measurable_id)
        change Measure.dirac (f h) {y | f h ≠ y} ≤ 0
        simp [Measure.dirac_apply' _ hset]
    _ = P A := by rw [lintegral_indicator hA, setLIntegral_const, one_mul]

theorem coupling_first_event_le {O : Type*} [MeasurableSpace O]
    (Q : Measure (O × O)) {S : Set O} (hS : MeasurableSet S) :
    Q.fst S ≤ Q.snd S + Q {z | z.1 ≠ z.2} := by
  rw [Measure.fst_apply hS, Measure.snd_apply hS]
  apply le_trans (measure_mono (show Prod.fst ⁻¹' S ⊆
      (Prod.snd ⁻¹' S) ∪ {z | z.1 ≠ z.2} from ?_)) (measure_union_le _ _)
  intro z hz
  by_cases he : z.1 = z.2
  · apply Or.inl
    change z.2 ∈ S
    change z.1 ∈ S at hz
    rwa [← he]
  · exact Or.inr he

theorem coupling_second_event_le {O : Type*} [MeasurableSpace O]
    (Q : Measure (O × O)) {S : Set O} (hS : MeasurableSet S) :
    Q.snd S ≤ Q.fst S + Q {z | z.1 ≠ z.2} := by
  rw [Measure.fst_apply hS, Measure.snd_apply hS]
  apply le_trans (measure_mono (show Prod.snd ⁻¹' S ⊆
      (Prod.fst ⁻¹' S) ∪ {z | z.1 ≠ z.2} from ?_)) (measure_union_le _ _)
  intro z hz
  by_cases he : z.1 = z.2
  · apply Or.inl
    change z.1 ∈ S
    change z.2 ∈ S at hz
    rwa [he]
  · exact Or.inr he

namespace CappedRaw.Rule
universe u v w
variable {Seed Reply : Type u} {State : Type v} {Query Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace Query]
  [MeasurableSpace Reply] [MeasurableSpace Output]
  (M : CappedRaw.Rule State Query Reply Output)
  (K : Kernel Query Reply) [IsMarkovKernel K]
  (hpos : ∀ s, K (M.query s) (Prod.mk s ⁻¹' M.acceptance) ≠ 0)

theorem cappedIdealCoupling_disagreement {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P]
    (hdiag : MeasurableSet {z : Output × Output | z.1 ≠ z.2}) :
    (M.cappedIdealCoupling K hpos hi n T P) {z | z.1 ≠ z.2} ≤
      ((M.policy initial hi n T).historyLaw P K T) {h | (M.state initial n T h).1 < n} := by
  apply completion_coupling_disagreement _ _ _ (M.policy initial hi n T).output_measurable
    (measurableSet_lt (M.state_measurable hi n T).fst measurable_const) _ hdiag
  intro h hh
  exact M.idealCompletionKernel_done K hpos (M.state initial n T h) (Nat.le_of_not_gt hh)

theorem cappedIdealCoupling_disagreement_probability {initial : Seed → State} (hi : Measurable initial)
    (n : ℕ) (P : Measure Seed) [IsProbabilityMeasure P]
    (hdiag : MeasurableSet {z : Output × Output | z.1 ≠ z.2})
    (hrej : ∀ t (h : AdaptiveKernel.History Seed Reply t),
      (K (M.query (M.state initial n t h).2)).real
        {r | (h, r) ∈ M.rejection initial n t} ≤ 1 / 16) :
    (M.cappedIdealCoupling K hpos hi n (4 * n) P).real {z | z.1 ≠ z.2} ≤
      ((2 : ℝ) ^ (8 * n))⁻¹ := by
  have h := ENNReal.toReal_mono (measure_ne_top ((M.policy initial hi n (4 * n)).historyLaw P K (4 * n)) _)
    (M.cappedIdealCoupling_disagreement K hpos hi n (4 * n) P hdiag)
  exact h.trans (M.failure_probability hi n (4 * n) P K hrej)

theorem capped_failure_le_ideal_plus_tail {initial : Seed → State} (hi : Measurable initial)
    (n : ℕ) (P : Measure Seed) [IsProbabilityMeasure P]
    (hdiag : MeasurableSet {z : Output × Output | z.1 ≠ z.2})
    (hrej : ∀ t (h : AdaptiveKernel.History Seed Reply t),
      (K (M.query (M.state initial n t h).2)).real
        {r | (h, r) ∈ M.rejection initial n t} ≤ 1 / 16)
    {S : Set Output} (hS : MeasurableSet S) :
    ((M.policy initial hi n (4 * n)).outputLaw P K).real S ≤
      (M.idealOutputLaw K hpos hi n P).real S + ((2 : ℝ) ^ (8 * n))⁻¹ := by
  let Q := M.cappedIdealCoupling K hpos hi n (4 * n) P
  have h := coupling_first_event_le Q hS
  rw [M.cappedIdealCoupling_fst, M.cappedIdealCoupling_snd] at h
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨measure_ne_top _ _, measure_ne_top Q _⟩) h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top Q _)] at hr
  have htail := M.cappedIdealCoupling_disagreement_probability K hpos hi n P hdiag hrej
  exact hr.trans (add_le_add_left htail _)

theorem ideal_capped_event_distance {initial : Seed → State} (hi : Measurable initial)
    (n : ℕ) (P : Measure Seed) [IsProbabilityMeasure P]
    (hdiag : MeasurableSet {z : Output × Output | z.1 ≠ z.2})
    (hrej : ∀ t (h : AdaptiveKernel.History Seed Reply t),
      (K (M.query (M.state initial n t h).2)).real
        {r | (h, r) ∈ M.rejection initial n t} ≤ 1 / 16)
    {S : Set Output} (hS : MeasurableSet S) :
    |((M.policy initial hi n (4 * n)).outputLaw P K).real S -
      (M.idealOutputLaw K hpos hi n P).real S| ≤ ((2 : ℝ) ^ (8 * n))⁻¹ := by
  have hfirst := M.capped_failure_le_ideal_plus_tail K hpos hi n P hdiag hrej hS
  let Q := M.cappedIdealCoupling K hpos hi n (4 * n) P
  have h := coupling_second_event_le Q hS
  rw [M.cappedIdealCoupling_fst, M.cappedIdealCoupling_snd] at h
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨measure_ne_top _ _, measure_ne_top Q _⟩) h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top Q _)] at hr
  have htail := M.cappedIdealCoupling_disagreement_probability K hpos hi n P hdiag hrej
  have hsecond := hr.trans (add_le_add_left htail _)
  change (M.idealOutputLaw K hpos hi n P).real S ≤
    ((M.policy initial hi n (4 * n)).outputLaw P K).real S + ((2 : ℝ) ^ (8 * n))⁻¹ at hsecond
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CappedRaw.Rule
end HeavyTail
