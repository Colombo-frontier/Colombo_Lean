import SampleReuse.CurvatureFirstQueryCounts
import SampleReuse.CurvatureFirstPolicy
import SampleReuse.OracleDerivativeCapsMeasurable
import SampleReuse.OracleDerivativeCapsFinish

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def cappedCurvatureFirstProgram {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH : ℕ) :=
  OracleDerivativeCaps.cap Prod.fst none Cg CH
    (curvatureFirstProgram (T := T) hBg hBH P ε γ scaleG scaleH signs m t s)

theorem cappedCurvatureFirstProgram_usesAtMost {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH : ℕ) :
    OracleProgram.UsesAtMost (Cg+CH)
      (cappedCurvatureFirstProgram (T := T) hBg hBH P ε γ scaleG scaleH signs m t s Cg CH) :=
  OracleDerivativeCaps.cap_usesAtMost _ _ _ _ _

theorem cappedCurvatureFirstProgram_separate_counts {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH n : ℕ) :
    let c := OracleDerivativeCaps.requestCounts Prod.fst (fun q tape => persistentReply F tape q) n
      (fun _ => tape) (cappedCurvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s Cg CH)
    c.1 ≤ Cg ∧ c.2 ≤ CH :=
  OracleDerivativeCaps.cap_requestCounts_le _ _ _ _ _ _ _ _

theorem cappedCurvatureFirstProgram_run {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH : ℕ)
    (hg : (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).1 ≤ Cg)
    (hH : (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).2 ≤ CH) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (cappedCurvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s Cg CH)
      (curvatureFirstCallTime hBg hBH P ε γ scaleG scaleH F tape signs m t s) =
      .done (curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m t s) := by
  apply OracleDerivativeCaps.cap_run_agreement
  · exact curvatureFirstProgram_run hBg hBH P ε γ scaleG scaleH F q₀ tape signs m t s
  · simpa only [curvatureFirstProgram_requestCounts hBg hBH P ε γ scaleG scaleH F q₀] using hg
  · simpa only [curvatureFirstProgram_requestCounts hBg hBH P ε γ scaleG scaleH F q₀] using hH

theorem cappedCurvatureFirstProgram_run_at_budget {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (Cg CH : ℕ)
    (hg : (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).1 ≤ Cg)
    (hH : (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).2 ≤ CH) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (cappedCurvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s Cg CH) (Cg+CH) =
      .done (curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m t s) := by
  apply OracleDerivativeCaps.cap_run_at_budget
  · exact curvatureFirstProgram_run hBg hBH P ε γ scaleG scaleH F q₀ tape signs m t s
  · simpa only [curvatureFirstProgram_requestCounts hBg hBH P ε γ scaleG scaleH F q₀] using hg
  · simpa only [curvatureFirstProgram_requestCounts hBg hBH P ε γ scaleG scaleH F q₀] using hH

theorem cappedCurvatureFirstProgram_measurableFamily {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (m t Cg CH : ℕ) :
    OracleProgram.MeasurableFamily q₀ none
      (fun w : (ℕ → Bool) × OptimizerCache d =>
        cappedCurvatureFirstProgram hBg hBH P ε γ scaleG scaleH w.1 m t w.2 Cg CH) :=
  OracleDerivativeCaps.cap_measurableFamily Prod.fst measurable_fst none
    (curvatureFirstProgram_measurableFamily hBg hBH P ε γ scaleG scaleH q₀ m t) Cg CH

end
end SampleReuse
