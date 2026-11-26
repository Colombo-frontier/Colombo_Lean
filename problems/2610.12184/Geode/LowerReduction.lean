import Geode.OracleModel

/-! Reduction from actual fixed-instance failure witnesses to minimax lower
bounds. `HorizonFailureWitness` is the explicitly stated construction requirement;
this file does not assert its existence or the unconditional main lower bound. -/

namespace Geode.OracleReplay

variable {Point Reply : Type*}

/-- Once an algorithm has stopped, granting more query fuel preserves its
entire history and output. -/
theorem run_add_fuel_of_finished (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (n m : ℕ) (h finalHistory : History Point Reply)
    (output : Point) (hf : run A respond n h = .finished finalHistory output) :
    run A respond (n + m) h = .finished finalHistory output := by
  induction n generalizing h with
  | zero =>
    cases hd : A.decide h with
    | stop x =>
      have heq : RunResult.finished h x = RunResult.finished finalHistory output := by
        simpa only [run, hd] using hf
      cases m <;> simpa only [Nat.zero_add, run, hd] using heq
    | query x => simp only [run, hd] at hf; cases hf
  | succ n ih =>
    cases hd : A.decide h with
    | stop x => simpa only [Nat.succ_add, run, hd] using hf
    | query x =>
      simp only [Nat.succ_add, run, hd]
      apply ih
      simpa only [run, hd] using hf

theorem run_mono_fuel_of_finished (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) {n N : ℕ} (hn : n ≤ N)
    (h finalHistory : History Point Reply) (output : Point)
    (hf : run A respond n h = .finished finalHistory output) :
    run A respond N h = .finished finalHistory output := by
  simpa only [Nat.add_sub_of_le hn] using
    run_add_fuel_of_finished A respond n (N - n) h finalHistory output hf

end Geode.OracleReplay

namespace Geode.Lorentz

open Geode.OracleReplay
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Guarantees.mono_budget {o : Point E} {R L ε : ℝ} {n N : ℕ}
    {A : FirstOrderAlgorithm E} (hA : Guarantees o R L ε n A) (hn : n ≤ N) :
    Guarantees o R L ε N A := by
  intro f hf O hO
  obtain ⟨h, output, hrun, hgap⟩ := hA f hf O hO
  exact ⟨h, output, run_mono_fuel_of_finished A (fixedResponder O) hn [] h output hrun,
    hgap⟩

theorem FeasibleBudget.mono_budget {o : Point E} {R L ε : ℝ} {n N : ℕ}
    (h : FeasibleBudget o R L ε n) (hn : n ≤ N) : FeasibleBudget o R L ε N := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA.mono_budget hn⟩

/-- The remaining resisting-oracle construction obligation: for every actual
history-dependent algorithm there is one admissible objective and one fixed,
globally legal oracle for which the budget is exhausted or the output gap is
at least twice the requested tolerance. Neither the objective nor this oracle
may change during the actual run. -/
def HorizonFailureWitness (o : Point E) (R L ε : ℝ) (T : ℕ) : Prop :=
  ∀ A : FirstOrderAlgorithm E,
    ∃ (f : Point E → ℝ) (O : Point E → FirstOrderReply E) (p : Point E),
      AdmissibleObjective o R L f ∧ LegalOracle f O ∧ (∀ y, f p ≤ f y) ∧
        RunFails (fun output => 2 * ε * L * R ≤ f output - f p)
          (run A (fixedResponder O) T [])

theorem not_feasible_of_failure_witness {o : Point E} {R L ε : ℝ} {T : ℕ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε)
    (hw : HorizonFailureWitness o R L ε T) : ¬ FeasibleBudget o R L ε T := by
  rintro ⟨A, hA⟩
  obtain ⟨f, O, p, hf, hO, hp, hfail⟩ := hw A
  obtain ⟨history, output, hrun, hgap⟩ := hA f hf O hO
  rw [hrun] at hfail
  change 2 * ε * L * R ≤ f output - f p at hfail
  have hgood := hgap p hp
  have hpos : 0 < ε * L * R := mul_pos (mul_pos hε hL) hR
  nlinarith

theorem queryComplexity_lower_of_failure_witness {o : Point E} {R L ε : ℝ} {T : ℕ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε)
    (hw : HorizonFailureWitness o R L ε T) :
    ((T + 1 : ℕ) : ℝ≥0∞) ≤ queryComplexity o R L ε := by
  apply queryComplexity_lower_of_no_budget
  intro N hN hfeasible
  exact not_feasible_of_failure_witness hR hL hε hw (hfeasible.mono_budget hN)

/-- Conditional bridge to the manuscript's uniform lower bound. The only
unfilled construction requirement is the explicitly supplied `hw`. -/
theorem uniform_lower_of_failure_witness {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hw : HorizonFailureWitness
      (origin : HyperbolicSpace (Geode.queryHorizon R ε + 2))
      R L ε (Geode.queryHorizon R ε)) :
    ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤
      uniformComplexity R L ε := by
  have hscalar : ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤
      ((Geode.queryHorizon R ε + 1 : ℕ) : ℝ≥0∞) := by
    apply ENNReal.ofReal_le_natCast.mpr
    exact_mod_cast (Geode.uniform_horizon_bound hR hε hεmax).le
  exact hscalar.trans ((queryComplexity_lower_of_failure_witness hR hL hε hw).trans
    (dimensionComplexity_le_uniform (by omega : 2 ≤ Geode.queryHorizon R ε + 2) R L ε))

end Geode.Lorentz
