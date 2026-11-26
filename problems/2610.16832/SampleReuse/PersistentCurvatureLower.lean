import SampleReuse.PersistentDeterministicLaw
import SampleReuse.RandomFrameUniformLower

open SecondOrder MeasureTheory
open scoped ENNReal
namespace SampleReuse
noncomputable section

/-- The deterministic curvature lower bound in the common persistent
stopping-algorithm interface. Its sample tape contains one-point samples;
arbitrary retained handles therefore change neither responses nor costs. -/
theorem persistent_curvature_uniform_lower (M : Parameters) :
    ∃ c C η : ℝ, 0 < c ∧ 0 < C ∧ 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      ∀ ε : ℝ, ε < M.gradientBound/8 → ∀ d : ℕ,
      ⌈C * (1 + Real.log (2/γ)/γ^4 + 1/γ^3)⌉₊ ≤ d →
      ∀ (H S Ξ : Type) [MeasurableSpace S] [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
        (_hP : MeasurableStoppingFamily P),
      (∀ f, Admissible (PMF.pure ()).toMeasure M f (fun _ : Unit => f) 0 →
        (2/3:ℝ) ≤ (μ.prod (iidSampleTapeLaw (PMF.pure ()))).real
          {w : Ξ × (ℕ → Unit) | (P w.1).Halts (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2 ∧
            IsSOSP f ε γ ((P w.1).outputFor (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2)}) →
      ∃ f, Admissible (PMF.pure ()).toMeasure M f (fun _ : Unit => f) 0 ∧
        ENNReal.ofReal (c/γ^3) ≤ ∫⁻ w : Ξ × (ℕ → Unit),
          (P w.1).extendedCost (fun x (_ : Unit) => RandomFrame.fullJet f x) w.2
          ∂μ.prod (iidSampleTapeLaw (PMF.pure ())) := by
  obtain ⟨c,C,η,hc,hC,hη,hbound⟩ := RandomFrame.deterministic_curvature_uniform_lower M
  refine ⟨c,C,η,hc,hC,hη,?_⟩
  intro γ hγ hγη ε hε d hd H S Ξ _ _ μ _ P hP hsolve
  obtain ⟨f,hf,hcost⟩ := hbound γ hγ hγη ε hε d hd Ξ μ
    (deterministicFullJetPolicy P hP) (fun f hf => by
      have hs := hsolve f hf
      rw [deterministicBridge_success_probability P hP f (IsSOSP f ε γ) μ] at hs
      exact hs)
  refine ⟨f,hf,?_⟩
  rw [deterministicBridge_expected P hP hf.population_smooth μ]
  exact hcost

end
end SampleReuse
