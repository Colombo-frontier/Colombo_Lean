import SampleReuse.PersistentSuccessProbability
import SecondOrder.FiniteSeedAveraging

open SecondOrder MeasureTheory
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {H S Ξ : Type} [Fintype H] [MeasurableSpace Ξ]

/-- The hidden target is selected after integrating the private seed, so
one common hard objective applies to the whole randomized policy. -/
theorem persistent_seed_exists_hard_target
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Ξ → PersistentFirstOrderPolicy d T H S)
    (hT : 0 < T) (A β R : ℝ) (hR : 2 ≤ R) (cap N : ℕ) (hcap0 : 0 < cap)
    (hbudget : 2*N ≤ T*cap)
    (hfast : ∀ ξ (i : Fin T),
      pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
        (persistentStageReached (P ξ) (persistentSourceHidden w) A β (persistentSourceTable w) i.succ N ∧
          persistentStageResponseCount (P ξ) (persistentSourceHidden w) A β
            (persistentSourceTable w) (i.val+1) N < cap)) ≤ 1/32)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ)) ≤ (d:ℝ))
    (success : (Fin (T+1) → Fin d → Bool) → Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x) = T+1)
    (hE : ∀ Θ (table : H → FirstOrderCoefficients d T R),
      MeasurableSet {ξ | success Θ (persistentOriginalOutput (P ξ) Θ A β table N)}) :
    ∃ Θ : Fin (T+1) → Fin d → Bool,
      (∫ ξ, pmfEventProbability (finitePiPMF (fun _ : H => firstOrderChainCoefficientLaw Θ R hR))
        (fun table => decide (success Θ (persistentOriginalOutput (P ξ) Θ A β table N))) ∂μ) < 1/4 := by
  apply finiteSeed_exists_hard_instance μ
    (finitePiPMF (fun _ : Fin (T+1) => PMF.uniformOfFintype (Fin d → Bool)))
    (fun Θ => finitePiPMF (fun _ : H => firstOrderChainCoefficientLaw Θ R hR))
    (fun ξ Θ table => success Θ (persistentOriginalOutput (P ξ) Θ A β table N)) hE
    (by norm_num : (1/8:ℝ) < 1/4)
  intro ξ
  have hb := persistent_original_success_one_eighth (P ξ) hT A β R hR cap N hcap0 hbudget
    (hfast ξ) hfar success hcomplete
  rw [← persistent_original_success_law (P ξ) A β R hR N success] at hb
  simpa only [persistentOriginalJointLaw,pmfEventProbability_mean,finiteConditionalPMF_mean] using hb

end
end SampleReuse
