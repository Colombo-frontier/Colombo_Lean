import SampleReuse.PersistentStopCoupling
import SampleReuse.PersistentSignStage

/-! Fast activation bound for an actual preallocated biased sign table.
The source is sampled once; all adaptive repetitions use that same source. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section
variable {d : ℕ} {Key : Type} [Fintype Key]
  [MeasurableSpace Key] [MeasurableSingletonClass Key]

def signTableFastSet {R : ℝ}
    (query : ∀ n, FiniteHistory Unit (Fin d → SignedCoefficient R) n → Key)
    (target : Key → Prop) (cap : ℕ)
    (points : ∀ n, FiniteHistory Unit (Fin d → SignedCoefficient R) n → Point d) (N : ℕ) :=
  kernelStoppedHitSet
    (quotaSafe (stageSelected (targetDisclosure query target)) cap
      (kernelHiddenEvent (signStageActivation points)))
    (quotaHit (stageSelected (targetDisclosure query target)) cap
      (kernelHiddenEvent (signStageActivation points))) N

/-- The source hidden block and its entire reusable table are drawn at
time zero. Activation before the response quota is bounded by 1/32. -/
theorem persistent_sign_table_fast_bound (R : ℝ) (hR : 2 ≤ R)
    (query : ∀ n, FiniteHistory Unit (Fin d → SignedCoefficient R) n → Key)
    (target : Key → Prop) (common : Key → PMF (Fin d → SignedCoefficient R))
    (a₀ : Fin d → SignedCoefficient R) (cap N : ℕ)
    (points : ∀ n, FiniteHistory Unit (Fin d → SignedCoefficient R) n → Point d)
    {L : ℝ} (hL : 0 < L)
    (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)))))
    (hbudget : 32 * ((cap : ℝ) * ((d : ℝ) / R ^ 2) + Real.log 2) ≤ L) :
    pmfEventProbability
      (seededTablePMF (finiteProdPMF (PMF.uniformOfFintype (Fin d → Bool)) (PMF.pure ()))
        (fun s => signStageTrueArray R hR target common s.1))
      (fun z => decide (tableHistory (liftPublicQuery query) z.1 z.2 N ∈
        signTableFastSet query target cap points N)) ≤ 1 / 32 := by
  let hq : ∀ n, Measurable (query n) := fun _ => measurable_of_countable _
  let selected := stageSelected (H := Fin d → Bool) (targetDisclosure query target)
  let hs := stageSelected_measurable (H := Fin d → Bool) (targetDisclosure query target)
    (targetDisclosure_measurable query hq target)
  let K := hiddenDisclosureKernel query hq (signStageTrueArray R hR target common)
  let dummy := fun n => Kernel.const (FiniteHistory Unit (Fin d → SignedCoefficient R) n) (Measure.dirac a₀)
  let E := kernelHiddenEvent (signStageActivation points)
  have hE : ∀ n, MeasurableSet (E n) := fun _ => Set.to_countable _ |>.measurableSet
  have hb := persistent_sign_stage_one_thirty_second (Measure.dirac ()) R hR query hq target common
    cap dummy points (fun _ => measurable_of_countable _) N hL hlog hbudget
  have ht := uncapped_quota_hit_le_capped_activation ((signLaw d).prod (Measure.dirac ())) K
    (hiddenIndependentKernel dummy) selected hs cap E hE N
  have hd : (adaptiveKernelLaw ((signLaw d).prod (Measure.dirac ())) K N).real
      (signTableFastSet query target cap points N) ≤ 1 / 32 := ht.trans hb
  have hl := hidden_fixed_table_kernel_law (PMF.uniformOfFintype (Fin d → Bool)) (PMF.pure ())
    query hq (signStageTrueArray R hR target common) N
  simp only [PMF.toMeasure_pure] at hl
  change _ = adaptiveKernelLaw ((signLaw d).prod (Measure.dirac ())) K N at hl
  rw [← hl] at hd
  rw [← pmfEventProbability_measure]
  simp only [decide_eq_true_eq]
  simpa only [measureReal_def, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet, Set.preimage_setOf_eq] using hd

end
end SampleReuse
