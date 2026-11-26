import SampleReuse.CurvatureFirstCapped
import SampleReuse.CurvatureFirstActualSuccess

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

/-- The concrete reply-only controller compiled to an oracle algorithm. The
sample loss and population function are not arguments of this construction. -/
def cappedCurvatureFirstAlgorithm {d T Bg BH : ℕ} (hBg : 0<Bg) (hBH : 0<BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH : ℕ) :=
  OracleProgram.algorithm q₀ (0,0) none
    (cappedCurvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s Cg CH)

theorem cappedCurvatureFirstAlgorithm_measurableFamily {d T Bg BH : ℕ} (hBg : 0<Bg) (hBH : 0<BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (m t Cg CH : ℕ) :
    MeasurableOracleAlgorithmFamily (fun w : (ℕ→Bool) × OptimizerCache d =>
      cappedCurvatureFirstAlgorithm hBg hBH P ε γ scaleG scaleH q₀ w.1 m t w.2 Cg CH) :=
  OracleProgram.algorithm_measurable (0,0)
    (cappedCurvatureFirstProgram_measurableFamily hBg hBH P ε γ scaleG scaleH q₀ m t Cg CH)

theorem cappedCurvatureFirstAlgorithm_finite_measurable {d T Bg BH M : ℕ} (hBg : 0<Bg) (hBH : 0<BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (x₀ : Point d) (Cg CH : ℕ) :
    MeasurableOracleAlgorithmFamily (fun w : Fin M→Bool =>
      cappedCurvatureFirstAlgorithm hBg hBH P ε γ scaleG scaleH q₀ (extendFiniteSigns w) M 0 (optimizerInitial x₀) Cg CH) := by
  apply OracleProgram.algorithm_measurable
  exact (cappedCurvatureFirstProgram_measurableFamily hBg hBH P ε γ scaleG scaleH q₀ M 0 Cg CH).comp
    (fun w : Fin M→Bool => (extendFiniteSigns w,optimizerInitial x₀))
    ((extendFiniteSigns_measurable M).prodMk measurable_const)

theorem cappedCurvatureFirstAlgorithm_output {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0<Bg) (hBH : 0<BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ→Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH N : ℕ) :
    let alg := cappedCurvatureFirstAlgorithm hBg hBH P ε γ scaleG scaleH q₀ signs m t s Cg CH
    alg.output N (persistentRun alg.toQueryPolicy F tape N) =
      OracleProgram.output none (OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
        (cappedCurvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s Cg CH) N) := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  exact OracleProgram.algorithm_output _ _ _ _ _ _ _

theorem cappedCurvatureFirstAlgorithm_output_agrees {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0<Bg) (hBH : 0<BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ→Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH : ℕ)
    (hg : (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).1≤Cg)
    (hH : (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).2≤CH) :
    let alg := cappedCurvatureFirstAlgorithm hBg hBH P ε γ scaleG scaleH q₀ signs m t s Cg CH
    alg.output (Cg+CH) (persistentRun alg.toQueryPolicy F tape (Cg+CH)) =
      curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m t s := by
  dsimp only
  rw [cappedCurvatureFirstAlgorithm_output,cappedCurvatureFirstProgram_run_at_budget hBg hBH P ε γ scaleG scaleH F q₀ tape signs m t s Cg CH hg hH]
  rfl

end
end SampleReuse
