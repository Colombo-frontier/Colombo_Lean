import SampleReuse.OracleBatchLaw
import Mathlib.MeasureTheory.Measure.Prod

/-! Freshness is derived from the immutable product sample tape. An actual
execution that has queried only past handles is independent of every disjoint
fresh block. Consequently a uniform fixed-history probability bound remains
valid after endpoints and batch size are chosen from that execution history. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical ENNReal

namespace SampleReuse
noncomputable section

def fillPartialTape {Ω : Type*} {H : ℕ} (past : Finset (Fin H)) (z₀ : Ω)
    (partialTape : past → Ω) (r : Fin H) : Ω :=
  if hr : r ∈ past then partialTape ⟨r, hr⟩ else z₀

theorem fillPartialTape_measurable {Ω : Type*} [MeasurableSpace Ω] {H : ℕ}
    (past : Finset (Fin H)) (z₀ : Ω) : Measurable (fillPartialTape past z₀) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r ∈ past
  · simpa only [fillPartialTape, dif_pos hr] using (measurable_pi_apply (⟨r, hr⟩ : past))
  · simp only [fillPartialTape, dif_neg hr]
    exact measurable_const

theorem history_independent_fresh_handles {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z₀ : Ω)
    (past : Finset (Fin H)) (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (handles : Fin b → Fin H) (hfresh : ∀ i, handles i ∉ past) :
    IndepFun history (fun tape i => tape (handles i)) (sampleTapeLaw H μ) := by
  let fresh := Finset.univ \ past
  have hd : Disjoint past fresh := Finset.disjoint_left.mpr (fun r hr hr' =>
    (Finset.mem_sdiff.mp hr').2 hr)
  have hi := iIndepFun.indepFun_finset past fresh hd (sampleTapeLaw_independent H μ)
    (fun r => measurable_pi_apply r)
  let historyFromPast : (past → Ω) → S := fun tape => history (fillPartialTape past z₀ tape)
  let freshExtract : (fresh → Ω) → SampleTape b Ω :=
    fun tape i => tape ⟨handles i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfresh i⟩⟩
  have hh' : Measurable historyFromPast := hh.comp (fillPartialTape_measurable past z₀)
  have hf' : Measurable freshExtract := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have he : ∀ tape : SampleTape H Ω,
      historyFromPast (fun r : past => tape r) = history tape := by
    intro tape
    apply hdep
    intro r hr
    simp only [fillPartialTape, dif_pos hr]
  exact (hi.comp hh' hf').congr (Filter.Eventually.of_forall he) (Filter.Eventually.of_forall (fun _ => rfl))

theorem history_fresh_handles_joint_law {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z₀ : Ω)
    (past : Finset (Fin H)) (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (handles : Fin b → Fin H) (hfresh : ∀ i, handles i ∉ past)
    (hinj : Function.Injective handles) :
    (sampleTapeLaw H μ).map (fun tape => (history tape, fun i => tape (handles i))) =
      ((sampleTapeLaw H μ).map history).prod (sampleTapeLaw b μ) := by
  have hi := history_independent_fresh_handles μ z₀ past history hh hdep handles hfresh
  have hm : Measurable (fun tape : SampleTape H Ω => fun i => tape (handles i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (handles i))
  rw [indepFun_iff_map_prod_eq_prod_map_map hh.aemeasurable hm.aemeasurable] at hi
  simpa only [sampleTapeLaw_selection μ handles hinj] using hi

/-- Uniform bounds may depend on the complete past history through the event
section; the fresh product block is independent after fixing that history. -/
theorem adaptive_fresh_event_bound {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z₀ : Ω)
    (past : Finset (Fin H)) (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (handles : Fin b → Fin H) (hfresh : ∀ i, handles i ∉ past)
    (hinj : Function.Injective handles) (bad : Set (S × SampleTape b Ω)) (hm : MeasurableSet bad)
    (δ : ℝ≥0∞) (hbound : ∀ s, sampleTapeLaw b μ {zs | (s, zs) ∈ bad} ≤ δ) :
    sampleTapeLaw H μ {tape | (history tape, fun i => tape (handles i)) ∈ bad} ≤ δ := by
  have hpair : Measurable (fun tape : SampleTape H Ω => (history tape, fun i => tape (handles i))) :=
    hh.prodMk (measurable_pi_lambda _ (fun i => measurable_pi_apply (handles i)))
  haveI : IsProbabilityMeasure ((sampleTapeLaw H μ).map history) :=
    isProbabilityMeasure_map hh.aemeasurable
  change (sampleTapeLaw H μ) ((fun tape => (history tape, fun i => tape (handles i))) ⁻¹' bad) ≤ δ
  rw [← Measure.map_apply hpair hm,
    history_fresh_handles_joint_law μ z₀ past history hh hdep handles hfresh hinj,
    Measure.prod_apply hm]
  exact (lintegral_mono (fun s => hbound s)).trans_eq (by simp)

theorem adaptive_fresh_event_real_bound {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z₀ : Ω)
    (past : Finset (Fin H)) (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (handles : Fin b → Fin H) (hfresh : ∀ i, handles i ∉ past)
    (hinj : Function.Injective handles) (bad : Set (S × SampleTape b Ω)) (hm : MeasurableSet bad)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ s, (sampleTapeLaw b μ).real {zs | (s, zs) ∈ bad} ≤ δ) :
    (sampleTapeLaw H μ).real {tape | (history tape, fun i => tape (handles i)) ∈ bad} ≤ δ := by
  have he := adaptive_fresh_event_bound μ z₀ past history hh hdep handles hfresh hinj bad hm
    (ENNReal.ofReal δ) (fun s => by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hbound s))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hδ)

theorem persistentRun_depends_on_past {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (n : ℕ) (past : Finset (Fin H))
    (hallowed : ∀ tape k, k < n → (P.query k (persistentRun P F tape k)).2.1 ∈ past)
    (tape tape' : SampleTape H Ω) (heq : ∀ r ∈ past, tape r = tape' r) :
    persistentRun P F tape n = persistentRun P F tape' n := by
  apply persistentRun_tape_congr
  intro k hk
  exact heq _ (hallowed tape k hk)

theorem persistentRun_fixed_measurable {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (hq : ∀ n, Measurable (P.query n))
    (hu : ∀ n, Measurable (fun w : S × PersistentReply d => P.update n w.1 w.2))
    (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2)) (n : ℕ) :
    Measurable (fun tape => persistentRun P F tape n) := by
  have hP : MeasurableQueryPolicyFamily (fun _ : Unit => P) :=
    ⟨measurable_const, fun n => (hq n).comp measurable_snd,
      fun n => (hu n).comp measurable_snd⟩
  exact (persistentRun_measurable _ hP F hg hH n).comp
    ((measurable_const (a := ())).prodMk measurable_id)

/-- Actual execution states are fresh-block independent; the dependence and
measurability premises are proved from the query/update policy and its trace. -/
theorem persistentRun_independent_fresh_handles {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {H d b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z₀ : Ω)
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (hq : ∀ n, Measurable (P.query n))
    (hu : ∀ n, Measurable (fun w : S × PersistentReply d => P.update n w.1 w.2))
    (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (n : ℕ) (past : Finset (Fin H))
    (hallowed : ∀ tape k, k < n → (P.query k (persistentRun P F tape k)).2.1 ∈ past)
    (handles : Fin b → Fin H) (hfresh : ∀ i, handles i ∉ past) :
    IndepFun (fun tape => persistentRun P F tape n) (fun tape i => tape (handles i))
      (sampleTapeLaw H μ) :=
  history_independent_fresh_handles μ z₀ past _
    (persistentRun_fixed_measurable P hq hu F hg hH n)
    (persistentRun_depends_on_past P F n past hallowed) handles hfresh

end
end SampleReuse
