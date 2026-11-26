import SampleReuse.CurvatureFirstAccuracyEvents
import SampleReuse.OracleSeedAveraging

open MeasureTheory SecondOrder
open scoped ENNReal Classical

namespace SampleReuse
noncomputable section

theorem probability_failure_of_success {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (p : A → Prop)
    (hm : MeasurableSet {a | p a}) {δ : ℝ} (hp : 1-δ ≤ μ.real {a | p a}) :
    μ.real {a | ¬ p a} ≤ δ := by
  change μ.real {a | p a}ᶜ ≤ δ
  rw [measureReal_compl hm,measureReal_univ_eq_one]
  linarith

theorem product_event_real_bound_of_left_sections {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (bad : Set (A × B)) (hm : MeasurableSet bad) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsections : ∀ b, μ.real {a | (a,b) ∈ bad} ≤ δ) :
    (μ.prod ν).real bad ≤ δ := by
  have hb : (μ.prod ν) bad ≤ ENNReal.ofReal δ := by
    rw [Measure.prod_apply_symm hm]
    apply (lintegral_mono (fun b => show μ ((fun a => (a,b)) ⁻¹' bad) ≤ ENNReal.ofReal δ from ?_)).trans_eq
      (by simp)
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hsections b)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hδ)

def MacroAccurate {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH ηG ηH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) : Prop :=
  MacroGradientAccurate hBg hBH P ε γ scaleG scaleH ηG f F x₀ tape signs ∧
    MacroHessianAccurate hBg hBH P ε γ scaleG scaleH ηH f F x₀ tape signs

theorem Admissible.macroAccurate_measurableSet {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH ηG ηH : ℝ)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (signs : A → ℕ → Bool) (hsigns : Measurable signs) :
    MeasurableSet {a | MacroAccurate hBg hBH P ε γ scaleG scaleH ηG ηH f F x₀ (tape a) (signs a)} :=
  (had.macroGradientAccurate_measurableSet hBg hBH ε γ scaleG scaleH ηG tape htape signs hsigns).inter
    (had.macroHessianAccurate_measurableSet hBg hBH ε γ scaleG scaleH ηH tape htape signs hsigns)

theorem Admissible.curvatureFirst_joint_accuracy_fixed_signs {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH : ℝ) (z₀ : Ω) {ηG ηH δG δH : ℝ}
    (hηG : 0 < ηG) (hηH : 0 < ηH) (hδG : 0 < δG) (hδH : 0 < δH)
    (hscaleG : scaleG = confidenceBatchScale d (ηG/(binaryDepth T+1)) (δG/(T+1)))
    (hscaleH : scaleH = confidenceBatchScale d (ηH/(binaryDepth T+1)) (δH/(T+1)))
    (hcapG : Bg = batchSize scaleG (P.gradientNoise^2))
    (hcapH : BH = batchSize scaleH (P.hessianNoise^2)) (signs : ℕ → Bool) :
    ((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).real
      {w | ¬ MacroAccurate hBg hBH P ε γ scaleG scaleH ηG ηH f F x₀
        (derivativeTapes w.1 w.2) signs} ≤ δG+δH := by
  let goodG := fun w : SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω =>
    MacroGradientAccurate hBg hBH P ε γ scaleG scaleH ηG f F x₀ (derivativeTapes w.1 w.2) signs
  let goodH := fun w : SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω =>
    MacroHessianAccurate hBg hBH P ε γ scaleG scaleH ηH f F x₀ (derivativeTapes w.1 w.2) signs
  have hmG : MeasurableSet {w | goodG w} := had.macroGradientAccurate_measurableSet
    hBg hBH ε γ scaleG scaleH ηG _ (derivativeTapes_measurable _ _) _ measurable_const
  have hmH : MeasurableSet {w | goodH w} := had.macroHessianAccurate_measurableSet
    hBg hBH ε γ scaleG scaleH ηH _ (derivativeTapes_measurable _ _) _ measurable_const
  have hG := product_event_real_bound_of_left_sections
    (sampleTapeLaw ((T+1)*Bg) μ) (sampleTapeLaw ((T+1)*BH) μ) {w | ¬goodG w} hmG.compl hδG.le
    (fun h => probability_failure_of_success _ (fun g => goodG (g,h))
      (hmG.preimage (measurable_id.prodMk measurable_const))
      (had.curvatureFirst_gradient_macro_accuracy hBg hBH ε γ scaleG scaleH z₀ hηG hδG hscaleG hcapG h signs))
  have hH := product_event_real_bound_of_sections
    (sampleTapeLaw ((T+1)*Bg) μ) (sampleTapeLaw ((T+1)*BH) μ) {w | ¬goodH w} hmH.compl hδH.le
    (fun g => probability_failure_of_success _ (fun h => goodH (g,h))
      (hmH.preimage (measurable_const.prodMk measurable_id))
      (had.curvatureFirst_hessian_accuracy hBg hBH ε γ scaleG scaleH z₀ hηH hδH hscaleH hcapH g signs))
  have he : {w | ¬ MacroAccurate hBg hBH P ε γ scaleG scaleH ηG ηH f F x₀
        (derivativeTapes w.1 w.2) signs} = {w | ¬goodG w} ∪ {w | ¬goodH w} := by
    ext w
    simp only [MacroAccurate,Set.mem_setOf_eq,Set.mem_union,not_and_or,goodG,goodH]
  rw [he]
  exact (measureReal_union_le _ _).trans (add_le_add hG hH)

/-- Both estimator confidence bounds hold under the actual joint law of
the two independent tapes and arbitrary independent private randomization. -/
theorem Admissible.curvatureFirst_joint_accuracy {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {d T Bg BH : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH : ℝ) (z₀ : Ω) {ηG ηH δG δH : ℝ}
    (hηG : 0 < ηG) (hηH : 0 < ηH) (hδG : 0 < δG) (hδH : 0 < δH)
    (hscaleG : scaleG = confidenceBatchScale d (ηG/(binaryDepth T+1)) (δG/(T+1)))
    (hscaleH : scaleH = confidenceBatchScale d (ηH/(binaryDepth T+1)) (δH/(T+1)))
    (hcapG : Bg = batchSize scaleG (P.gradientNoise^2))
    (hcapH : BH = batchSize scaleH (P.hessianNoise^2))
    (ν : Measure A) [IsProbabilityMeasure ν] (signs : A → ℕ → Bool) (hsigns : Measurable signs) :
    (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod ν).real
      {w | ¬ MacroAccurate hBg hBH P ε γ scaleG scaleH ηG ηH f F x₀
        (derivativeTapes w.1.1 w.1.2) (signs w.2)} ≤ δG+δH := by
  have hm : MeasurableSet {w : (SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω) × A |
      MacroAccurate hBg hBH P ε γ scaleG scaleH ηG ηH f F x₀
        (derivativeTapes w.1.1 w.1.2) (signs w.2)} :=
    had.macroAccurate_measurableSet hBg hBH ε γ scaleG scaleH ηG ηH
      _ ((derivativeTapes_measurable _ _).comp measurable_fst) _ (hsigns.comp measurable_snd)
  apply product_event_real_bound_of_left_sections _ ν _ hm.compl (add_nonneg hδG.le hδH.le)
  intro a
  exact had.curvatureFirst_joint_accuracy_fixed_signs hBg hBH ε γ scaleG scaleH z₀
    hηG hηH hδG hδH hscaleG hscaleH hcapG hcapH (signs a)

end
end SampleReuse
