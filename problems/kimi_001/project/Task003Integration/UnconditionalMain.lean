import Task003Integration.ProtasovBridge
import Task003Integration.ZhangBridge

namespace Task003.UnconditionalMain
open Task003.OracleModel

/-- The normalized paper main theorem with both literature inputs proved. -/
theorem normalized_main_unconditional
    (c0 : ℝ) (hc0 : 0 < c0) (hc0max : c0 ≤ 1 / 8) : FullJointProfile c0 :=
  Task003.LiteratureMain.normalized_main_from_literature
    Task003Integration.zhangLiteratureInput_proved
    Task003Integration.protasovLiteratureInput_proved c0 hc0 hc0max

/-- The original-scale minimax theorem, with no Zhang or Protasov hypotheses. -/
theorem scaled_main_unconditional
    (c0 : ℝ) (hc0 : 0 < c0) (hc0max : c0 ≤ 1 / 8) :
    ∃ (D : ℕ) (a b : ℝ), 0 < D ∧ 0 < a ∧ 0 < b ∧
      ∀ (d : ℕ), D ≤ d → ∀ (L R ε : ℝ), 0 < L → 0 < R →
        0 < ε / (L * R) → ε / (L * R) ≤ c0 →
        ∃ N : ℕ, minimaxBudget d L R ε = some N ∧
          a * profileQ d (ε / (L * R)) / (profileLambda d (ε / (L * R))) ^ 2 ≤ (N : ℝ) ∧
          (N : ℝ) ≤ b * profileQ d (ε / (L * R)) * (profileLambda d (ε / (L * R))) ^ 2 :=
  Task003.LiteratureMain.scaled_main_from_literature
    Task003Integration.zhangLiteratureInput_proved
    Task003Integration.protasovLiteratureInput_proved c0 hc0 hc0max

/-- A closed, assumption-free endpoint at the paper's fixed normalized cutoff. -/
theorem paper_main_unconditional : FullJointProfile (1 / 8) :=
  normalized_main_unconditional (1 / 8) (by norm_num) (by norm_num)

end Task003.UnconditionalMain
