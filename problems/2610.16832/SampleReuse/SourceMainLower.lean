import SampleReuse.PersistentMainLower
import SampleReuse.LowerDimensionEnvelope
import SampleReuse.SeparateOracleBridge

open SecondOrder MeasureTheory
open scoped ENNReal

namespace SampleReuse
noncomputable section

/-- The manuscript's main lower bound, including a single threshold with
the claimed dimension envelope and the stronger unit-cost full-jet oracle. -/
theorem source_main_lower_full_jet (M : Parameters) :
    ∃ c Cd ε₀ γ₀ : ℝ, 0 < c ∧ 0 < Cd ∧ 0 < ε₀ ∧ 0 < γ₀ ∧
      ∀ ε γ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < γ → γ < γ₀ →
      ∃ dstar : ℕ,
        (dstar : ℝ) ≤ Cd*(1+M.gap*(slowBlockSize M ε : ℝ)^(3/4 : ℝ)/ε+
          Real.log (2/γ)/γ^4+1/γ^3) ∧
      ∀ d : ℕ, dstar ≤ d →
      ∀ (H S Ξ : Type) [MeasurableSpace S] [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S),
      MeasurableStoppingFamily P → OperationallyMeasurable P →
      SolvesFiniteInstances (M := M) μ P ε γ →
      ∃ I : FiniteScalarInstance M d,
        ENNReal.ofReal (c*sourceLowerEnvelope M ε γ) ≤ finiteInstanceCost μ P I := by
  obtain ⟨c,C,ε₀,γ₀,hc,hC,hε₀,hγ₀,hmain⟩ := persistent_main_lower M
  obtain ⟨η,hη,hsmall⟩ := slow_calibrated_conditions_small M
  refine ⟨c,C+1,min ε₀ η,min γ₀ 1,hc,by linarith,
    lt_min hε₀ hη,lt_min hγ₀ (by norm_num),?_⟩
  intro ε γ hε he hγ hg
  refine ⟨lowerDimensionThreshold M C ε γ,
    lowerDimensionThreshold_source_bound M hC.le
      (hsmall ε hε (he.trans (min_le_right _ _))) hγ
      ((hg.trans_le (min_le_right _ _)).le),?_⟩
  intro d hd H S Ξ _ _ μ _ P hmeas hop hsolve
  exact hmain ε γ hε (he.trans (min_le_left _ _)) hγ
    (hg.trans_le (min_le_left _ _)) d hd H S Ξ μ P hmeas hop hsolve

def separateFiniteInstanceCost {M : Parameters} {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ)
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (I : FiniteScalarInstance M d) : ℝ≥0∞ :=
  ∫⁻ w : Ξ × (ℕ → I.Sample), (P w.1).extendedCost (separateSampleReply I.sample) w.2
    ∂μ.prod (iidSampleTapeLaw I.law)

def SolvesSeparateFiniteInstances {M : Parameters} {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ)
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (ε γ : ℝ) : Prop :=
  ∀ I : FiniteScalarInstance M d, (2/3 : ℝ) ≤
    (μ.prod (iidSampleTapeLaw I.law)).real {w : Ξ × (ℕ → I.Sample) |
      (P w.1).Halts (separateSampleReply I.sample) w.2 ∧
      IsSOSP I.population ε γ ((P w.1).outputFor (separateSampleReply I.sample) w.2)}

theorem toFullJetStopping_solves {M : Parameters} {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ)
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (ε γ : ℝ) (hsolve : SolvesSeparateFiniteInstances (M := M) μ P ε γ) :
    SolvesFiniteInstances (M := M) μ (fun ξ => toFullJetStopping (P ξ)) ε γ := by
  intro I
  change (2/3 : ℝ) ≤ (μ.prod (iidSampleTapeLaw I.law)).real
    {w : Ξ × (ℕ → I.Sample) |
      (toFullJetStopping (P w.1)).Halts (fun x z => richReply I.sample z x) w.2 ∧
      IsSOSP I.population ε γ ((toFullJetStopping (P w.1)).outputFor
        (fun x z => richReply I.sample z x) w.2)}
  simp only [toFullJetStopping_halts,toFullJetStopping_outputFor]
  exact hsolve I

theorem toFullJetStopping_expectedCost {M : Parameters} {d : ℕ} {H S Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ)
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (I : FiniteScalarInstance M d) :
    finiteInstanceCost μ (fun ξ => toFullJetStopping (P ξ)) I = separateFiniteInstanceCost μ P I := by
  unfold finiteInstanceCost separateFiniteInstanceCost finiteInstanceReply
  simp only [toFullJetStopping_extendedCost]

/-- The same lower bound applies to the source oracle, which returns only
the requested gradient or Hessian and charges each such evaluation once. -/
theorem source_main_lower_separate (M : Parameters) :
    ∃ c Cd ε₀ γ₀ : ℝ, 0 < c ∧ 0 < Cd ∧ 0 < ε₀ ∧ 0 < γ₀ ∧
      ∀ ε γ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < γ → γ < γ₀ →
      ∃ dstar : ℕ,
        (dstar : ℝ) ≤ Cd*(1+M.gap*(slowBlockSize M ε : ℝ)^(3/4 : ℝ)/ε+
          Real.log (2/γ)/γ^4+1/γ^3) ∧
      ∀ d : ℕ, dstar ≤ d →
      ∀ (H S Ξ : Type) [MeasurableSpace S] [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S),
      MeasurableStoppingFamily P → SeparateOperationallyMeasurable P →
      SolvesSeparateFiniteInstances (M := M) μ P ε γ →
      ∃ I : FiniteScalarInstance M d,
        ENNReal.ofReal (c*sourceLowerEnvelope M ε γ) ≤ separateFiniteInstanceCost μ P I := by
  obtain ⟨c,Cd,ε₀,γ₀,hc,hCd,hε₀,hγ₀,hmain⟩ := source_main_lower_full_jet M
  refine ⟨c,Cd,ε₀,γ₀,hc,hCd,hε₀,hγ₀,?_⟩
  intro ε γ hε he hγ hg
  obtain ⟨dstar,hdstar,hmain⟩ := hmain ε γ hε he hγ hg
  refine ⟨dstar,hdstar,?_⟩
  intro d hd H S Ξ _ _ μ _ P hmeas hop hsolve
  obtain ⟨I,hI⟩ := hmain d hd H S Ξ μ (fun ξ => toFullJetStopping (P ξ))
    (toFullJetStopping_measurable P hmeas) (toFullJetStopping_operational P hop)
    (toFullJetStopping_solves μ P ε γ hsolve)
  exact ⟨I,(toFullJetStopping_expectedCost μ P I) ▸ hI⟩

end
end SampleReuse
