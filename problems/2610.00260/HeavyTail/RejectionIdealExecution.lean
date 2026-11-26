import HeavyTail.RejectionIdealKernel
import HeavyTail.AdaptiveKernelRejection
import HeavyTail.AdaptiveKernelOutputKernel

/-! The raw-prefix process completed by fresh accepted rounds has exactly the
ideal accepted-process output law. This is an actual kernel execution identity,
and does not condition the ideal law on successful completion of the raw cap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace HeavyTail.CappedRaw.Rule
universe u v w
variable {Seed Reply : Type u} {State : Type v} {Query Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace Query]
  [MeasurableSpace Reply] [MeasurableSpace Output]
  (M : CappedRaw.Rule State Query Reply Output)
  (K : Kernel Query Reply) [IsMarkovKernel K]
  (hpos : ∀ s, K (M.query s) (Prod.mk s ⁻¹' M.acceptance) ≠ 0)

theorem idealCompletionKernel_average {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P] (t : ℕ)
    {S : Set Output} (hS : MeasurableSet S) :
    (∫⁻ h, M.idealCompletionKernel K hpos n (M.state initial n t h) S
      ∂(M.policy initial hi n T).historyLaw P K t) =
      ∫⁻ s, M.idealOutputKernel K hpos n (initial s) S ∂P := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm : Measurable (fun h : AdaptiveKernel.History Seed Reply (t + 1) =>
        M.idealCompletionKernel K hpos n (M.state initial n (t + 1) h) S) :=
      ((M.idealCompletionKernel K hpos n).measurable_coe hS).comp (M.state_measurable hi n (t + 1))
    rw [AdaptiveKernel.Policy.historyLaw_succ]
    refine (Measure.lintegral_compProd (μ := (M.policy initial hi n T).historyLaw P K t)
      (κ := (M.policy initial hi n T).replyKernel K t) hm).trans ?_
    calc
      _ = ∫⁻ h, M.idealCompletionKernel K hpos n (M.state initial n t h) S
          ∂(M.policy initial hi n T).historyLaw P K t := by
        apply lintegral_congr
        intro h
        exact M.idealCompletionKernel_harmonic K hpos n (M.state initial n t h) hS
      _ = _ := ih

def idealOutputLaw {initial : Seed → State} (hi : Measurable initial) (n : ℕ)
    (P : Measure Seed) : Measure Output :=
  (M.idealOutputKernel K hpos n).comap initial hi ∘ₘ P

instance idealOutputLaw_probability {initial : Seed → State} (hi : Measurable initial)
    (n : ℕ) (P : Measure Seed) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (M.idealOutputLaw K hpos hi n P) := by
  unfold idealOutputLaw
  infer_instance

def completionAfterHistory {initial : Seed → State} (hi : Measurable initial) (n t : ℕ) :
    Kernel (AdaptiveKernel.History Seed Reply t) Output :=
  (M.idealCompletionKernel K hpos n).comap (M.state initial n t) (M.state_measurable hi n t)

instance completionAfterHistory_markov {initial : Seed → State} (hi : Measurable initial)
    (n t : ℕ) : IsMarkovKernel (M.completionAfterHistory K hpos hi n t) := by
  unfold completionAfterHistory
  infer_instance

theorem completionAfterHistory_law {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P] (t : ℕ) :
    M.completionAfterHistory K hpos hi n t ∘ₘ (M.policy initial hi n T).historyLaw P K t =
      M.idealOutputLaw K hpos hi n P := by
  ext S hS
  rw [Measure.bind_apply hS (M.completionAfterHistory K hpos hi n t).aemeasurable,
    idealOutputLaw, Measure.bind_apply hS (Kernel.aemeasurable _)]
  exact M.idealCompletionKernel_average K hpos hi n T P t hS

def cappedIdealCoupling {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) : Measure (Output × Output) :=
  (((M.policy initial hi n T).historyLaw P K T).compProd
    (M.completionAfterHistory K hpos hi n T)).map
      (fun z => ((M.policy initial hi n T).output z.1, z.2))

instance cappedIdealCoupling_probability {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (M.cappedIdealCoupling K hpos hi n T P) := by
  unfold cappedIdealCoupling
  apply isProbabilityMeasure_map
  exact (((M.policy initial hi n T).output_measurable.comp measurable_fst).prodMk measurable_snd).aemeasurable

theorem cappedIdealCoupling_fst {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P] :
    (M.cappedIdealCoupling K hpos hi n T P).fst = (M.policy initial hi n T).outputLaw P K := by
  have hm : Measurable (fun z : AdaptiveKernel.History Seed Reply T × Output =>
      ((M.policy initial hi n T).output z.1, z.2)) :=
    ((M.policy initial hi n T).output_measurable.comp measurable_fst).prodMk measurable_snd
  rw [Measure.fst, cappedIdealCoupling, Measure.map_map measurable_fst hm]
  change _ = ((M.policy initial hi n T).historyLaw P K T).map (M.policy initial hi n T).output
  rw [show (Prod.fst ∘ fun z => ((M.policy initial hi n T).output z.1, z.2)) =
    (M.policy initial hi n T).output ∘ Prod.fst from rfl,
    ← Measure.map_map (M.policy initial hi n T).output_measurable measurable_fst]
  rw [← Measure.fst, Measure.fst_compProd]

theorem cappedIdealCoupling_snd {initial : Seed → State} (hi : Measurable initial)
    (n T : ℕ) (P : Measure Seed) [IsProbabilityMeasure P] :
    (M.cappedIdealCoupling K hpos hi n T P).snd = M.idealOutputLaw K hpos hi n P := by
  have hm : Measurable (fun z : AdaptiveKernel.History Seed Reply T × Output =>
      ((M.policy initial hi n T).output z.1, z.2)) :=
    ((M.policy initial hi n T).output_measurable.comp measurable_fst).prodMk measurable_snd
  rw [Measure.snd, cappedIdealCoupling, Measure.map_map measurable_snd hm]
  change (((M.policy initial hi n T).historyLaw P K T).compProd
    (M.completionAfterHistory K hpos hi n T)).snd = _
  rw [Measure.snd_compProd, M.completionAfterHistory_law]

end HeavyTail.CappedRaw.Rule
