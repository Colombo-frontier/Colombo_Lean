import SampleReuse.PersistentCapLaw
import SampleReuse.PersistentOutputPolicy
import SampleReuse.PersistentSeedLower

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

abbrev FirstOrderStoppingAlgorithm (d T : ℕ) (H S : Type) :=
  PersistentStoppingAlgorithm (Point (FirstOrderDimension d T)) H
    (RichReply (FirstOrderDimension d T)) (Point (FirstOrderDimension d T)) S

def firstOrderStoppingCapPolicy {d T : ℕ} {H S : Type}
    (P : FirstOrderStoppingAlgorithm d T H S) (N : ℕ) :=
  persistentOutputPolicy (normalizePersistentAlgorithm N P.cap) N

/-- The full operational expected-budget reduction. Arbitrary opaque labels
are normalized only at evaluation, internal coins are averaged before the
target is selected, and samples live on one genuine infinite iid tape. -/
theorem persistent_stopping_expected_lower {d T : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Ξ → FirstOrderStoppingAlgorithm d T H S)
    (hT : 0 < T) (A β R : ℝ) (hR : 2 ≤ R) (cap N : ℕ) (hcap0 : 0 < cap)
    (hbudget : 2*N ≤ T*cap)
    (hfast : ∀ ξ (i : Fin T),
      pmfEventProbability (persistentSourceLaw d T (Fin (N+1)) R hR) (fun w => decide
        (persistentStageReached (firstOrderStoppingCapPolicy (P ξ) N)
          (persistentSourceHidden w) A β (persistentSourceTable w) i.succ N ∧
          persistentStageResponseCount (firstOrderStoppingCapPolicy (P ξ) N)
            (persistentSourceHidden w) A β (persistentSourceTable w) (i.val+1) N < cap)) ≤ 1/32)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ)) ≤ (d:ℝ))
    (success : (Fin (T+1) → Fin d → Bool) → Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x) = T+1)
    (hE : ∀ Θ (table : Fin (N+1) → FirstOrderCoefficients d T R),
      MeasurableSet {ξ | success Θ (persistentOriginalOutput
        (firstOrderStoppingCapPolicy (P ξ) N) Θ A β table N)})
    (hs : ∀ Θ n, Measurable (fun w : Ξ × (ℕ → FirstOrderCoefficients d T R) =>
      (P w.1).stopOnRun (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) w.2 n))
    (hsolve : ∀ Θ, (2/3:ℝ) ≤
      (μ.prod (iidSampleTapeLaw (firstOrderChainCoefficientLaw Θ R hR))).real
        {w : Ξ × (ℕ → FirstOrderCoefficients d T R) |
          (P w.1).Halts (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) w.2 ∧
          success Θ ((P w.1).outputFor (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) w.2)}) :
    ∃ Θ : Fin (T+1) → Fin d → Bool,
      (N+1:ℕ) * ENNReal.ofReal (5/12) ≤
        ∫⁻ w : Ξ × (ℕ → FirstOrderCoefficients d T R),
          (P w.1).extendedCost (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) w.2
          ∂μ.prod (iidSampleTapeLaw (firstOrderChainCoefficientLaw Θ R hR)) := by
  obtain ⟨Θ,hΘ⟩ := persistent_seed_exists_hard_target μ
    (fun ξ => firstOrderStoppingCapPolicy (P ξ) N) hT A β R hR cap N hcap0 hbudget
    hfast hfar success hcomplete hE
  refine ⟨Θ,?_⟩
  have he (table : Fin (N+1) → FirstOrderCoefficients d T R) := hE Θ table
  simp only [firstOrderStoppingCapPolicy,persistentOutputPolicy_firstOrder] at he hΘ
  have hh := persistent_expected_calls_from_finite_cap μ P
    (fun x z => richReply (scaledFirstOrderSample Θ A β) z x)
    (firstOrderChainCoefficientLaw Θ R hR) N (success Θ) (hs Θ) he (hsolve Θ) hΘ.le
  norm_num at hh ⊢
  exact hh

end
end SampleReuse
