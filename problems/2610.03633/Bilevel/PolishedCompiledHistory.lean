import Bilevel.PolishedCompiledHistoryBind
import Bilevel.PolishedCompiledHistoryChoose

/-! Arbitrary-history-kernel operational compiler correctness. The summary
is constructed from syntax; no common-seed realization, supplied stopping
law, or assumed compiled-program budget is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory
open OracleCode Stateful HistoryProgram PolishedHistory
set_option autoImplicit false
variable {Q O A B H : Space}

def compileSummary (R : HistoryProgram.Oracle Q O H) (q₀ : Q) (o₀ : O) :
    {A B : Space} → (c : Code Q O A B) → Summary (compile q₀ o₀ c) c R
  | _,_,.pure f hf => Summary.pure R q₀ f hf
  | _,_,.call => Summary.call R o₀
  | _,_,.bind p q => Summary.bind (compileSummary R q₀ o₀ p) (compileSummary R q₀ o₀ q)
  | _,_,.reparam p f hf => Summary.reparam (compileSummary R q₀ o₀ p) f hf
  | _,_,.choose p n hn => Summary.choose (fun i => compile q₀ o₀ (p i)) p R
      (fun i => compileSummary R q₀ o₀ (p i)) n hn

/-- For every history-dependent conditional law and private input law, the
actual compiled first-halt original-call cost is bounded by its denotation. -/
theorem compiled_stopped_calls_le (R : HistoryProgram.Oracle Q O H) (q₀ : Q) (o₀ : O)
    (c : Code Q O A B) (ρ : Measure A) (h₀ : H) :
    (∫⁻ w,HistoryProgram.totalCalls (compile q₀ o₀ c).program w
      ∂trajectoryLaw (compile q₀ o₀ c).program R ρ (compile q₀ o₀ c).start h₀)≤
    ∫⁻ a,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀) ∂ρ :=
  (compileSummary R q₀ o₀ c).stopped_calls_le_denote ρ h₀

/-- Actual stopped risk of the compiled code is bounded by the exact same
history-dependent denotation used for the compositional stochastic proof. -/
theorem compiled_stopped_loss_le (R : HistoryProgram.Oracle Q O H) (q₀ : Q) (o₀ : O)
    (c : Code Q O A B) (ρ : Measure A) (h₀ : H)
    (hcost : (∫⁻ a,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀) ∂ρ)≠⊤)
    (loss : B → ℝ) (hloss : Measurable loss) :
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput (compile q₀ o₀ c).program w))
      ∂trajectoryLaw (compile q₀ o₀ c).program R ρ (compile q₀ o₀ c).start h₀)≤
    ∫⁻ a,∫⁻ y,ENNReal.ofReal (loss y.1)
      ∂(OracleCode.History.denote R.law R.update R.update_measurable c).law (a,h₀) ∂ρ :=
  (compileSummary R q₀ o₀ c).stopped_loss_le_denote ρ h₀ hcost loss hloss

end Bilevel.PolishedCompiledHistory
