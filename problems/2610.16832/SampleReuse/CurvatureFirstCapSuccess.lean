import SampleReuse.CurvatureFirstCapEvents
import SampleReuse.CurvatureFirstAlgorithm

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

/-- The compiled output after enough bookkeeping steps to finish. Execution
stops at the first finished program; subsequent bookkeeping does not request
oracle evaluations. -/
def cappedCurvatureFirstOutput {Ω : Type} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (x₀ : Point d) (Cg CH : ℕ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (bits : Fin M → Bool) : Option (Point d) :=
  let alg := cappedCurvatureFirstAlgorithm hBg hBH P ε γ scaleG scaleH q₀
    (extendFiniteSigns bits) M 0 (optimizerInitial x₀) Cg CH
  alg.output (Cg+CH) (persistentRun alg.toQueryPolicy F tape (Cg+CH))

/-- Actual capped success probability, with every confidence, stopping and
query-overflow term derived from the common scalar-loss model. -/
theorem Admissible.curvatureFirst_cap_success {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (hsg : 0 ≤ scaleG) (hsh : 0 ≤ scaleH) (z₀ : Ω) {δG δH : ℝ}
    (hδG : 0 < δG) (hδH : 0 < δH)
    (hscaleG : scaleG = confidenceBatchScale d ((ε/4)/(binaryDepth T+1)) (δG/(T+1)))
    (hscaleH : scaleH = confidenceBatchScale d ((γ/4)/(binaryDepth T+1)) (δH/(T+1)))
    (hcapG : Bg = batchSize scaleG (P.gradientNoise^2))
    (hcapH : BH = batchSize scaleH (P.hessianNoise^2))
    (hM : 0 < M) (horizon : M ≤ T+1) (depth : ℕ) (hd : M < 2^depth)
    (Cg CH : ℕ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) :
    1-((δG+δH)+P.gap/(optimizerMinDecrease P ε γ*M)+
      optimizerGradientExpectedBudget P ε γ scaleG depth/((Cg:ℝ)+1)+
      optimizerHessianExpectedBudget P ε γ scaleH depth/((CH:ℝ)+1)) ≤
    (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure).real {w | ∃ x,
        cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH
          (derivativeTapes w.1.1 w.1.2) w.2 = some x ∧ IsSOSP f ε γ x} := by
  let A := (SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω) × (Fin M → Bool)
  let law := ((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
    (PMF.uniformOfFintype (Fin M → Bool)).toMeasure
  let tape (w : A) := derivativeTapes w.1.1 w.1.2
  let good (w : A) := MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀
    (tape w) (extendFiniteSigns w.2)
  let out (w : A) := curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F
    (tape w) M 0 (optimizerInitial x₀) w.2
  let cout (w : A) := cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH (tape w) w.2
  let counts (w : A) := curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F
    (tape w) (extendFiniteSigns w.2) M 0 (optimizerInitial x₀)
  have htape : Measurable tape := (derivativeTapes_measurable _ _).comp measurable_fst
  have hsign : Measurable (fun w : A => extendFiniteSigns w.2) :=
    (extendFiniteSigns_measurable M).comp measurable_snd
  have hg : MeasurableSet {w | good w} := had.macroAccurate_measurableSet hBg hBH ε γ scaleG scaleH
    (ε/4) (γ/4) tape htape _ hsign
  have ho : Measurable out := curvatureFirstFiniteExecute_measurable hBg hBH P ε γ scaleG scaleH F
    had.gradient_measurable had.hessian_measurable tape htape _ measurable_snd x₀
  have hc : Measurable counts := curvatureFirstDerivativeCounts_measurable hBg hBH P ε γ scaleG scaleH F
    had.gradient_measurable had.hessian_measurable tape htape _ hsign M 0 _ measurable_const
  have hcontrolled : MeasurableSet {w | good w ∧ ¬out w = none ∧ (counts w).1 ≤ Cg ∧ (counts w).2 ≤ CH} :=
    hg.inter ((ho (optimizerOutput_none_measurableSet d)).compl.inter
      ((measurableSet_le hc.fst measurable_const).inter (measurableSet_le hc.snd measurable_const)))
  apply capped_success_probability_of_events law good (fun w => out w = none) out cout
    (fun o => ∃ x, o = some x ∧ IsSOSP f ε γ x) (fun w => (counts w).1) (fun w => (counts w).2)
    Cg CH hcontrolled
  · exact had.curvatureFirst_joint_accuracy hBg hBH ε γ scaleG scaleH z₀
      (by positivity) (by positivity) hδG hδH hscaleG hscaleH hcapG hcapH
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure extendFiniteSigns (extendFiniteSigns_measurable M)
  · exact had.curvatureFirst_joint_exhaustion hBg hBH hε hγ scaleG scaleH hM horizon
  · exact had.curvatureFirst_gradient_cap_probability hBg hBH hε hγ scaleG scaleH hsg hcapG horizon depth hd Cg
  · exact had.curvatureFirst_hessian_cap_probability hBg hBH hε hγ scaleG scaleH hsh hcapH horizon depth hd CH
  · intro w hgood hn
    cases he : out w with
    | none => exact False.elim (hn he)
    | some x =>
      refine ⟨x,rfl,?_⟩
      exact macroAccurate_output_sosp hBg hBH P ε γ scaleG scaleH f F x₀ (tape w) w.2 horizon hgood he
  · intro w hcg hch
    have he := cappedCurvatureFirstAlgorithm_output_agrees hBg hBH P ε γ scaleG scaleH F q₀
      (tape w) (extendFiniteSigns w.2) M 0 (optimizerInitial x₀) Cg CH hcg hch
    have hf := curvatureFirstFiniteExecute_eq hBg hBH P ε γ scaleG scaleH F (tape w)
      (extendFiniteSigns w.2) M 0 (optimizerInitial x₀) w.2
      (fun i => by simp only [Nat.zero_add,extendFiniteSigns,dif_pos i.isLt])
    exact he.trans hf.symm

end
end SampleReuse
