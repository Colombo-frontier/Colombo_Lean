import HeavyTail.CompositeStagePolicy
import HeavyTail.FiniteAverages

/-! The stored accumulator is the actual accepted-proximal-point average.
Feasibility and online-to-batch Jensen bounds are proved along every raw
history, including rejected rounds and absorption after the target count. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace HeavyTail.PublicProblem
universe u
variable {E W : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace W]
  {θ : OracleParameters}

def stageStateInvariant (B : PublicProblem E θ) (s : CompositeStageState W E) : Prop :=
  (s.2.2 = 0 → s.2.1 = 0) ∧ (0 < s.2.2 → stageAverage s ∈ B.S)

theorem stage_update_invariant (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R)
    (s : CompositeStageState W E) (g : E) (hs : B.stageStateInvariant s) :
    B.stageStateInvariant ((B.stageRule hR hn τ L).update (s, g)) := by
  constructor
  · change s.2.2 + 1 = 0 → _
    omega
  · intro _
    exact runningAverage_next_mem B.h_convex.1 hs.1 hs.2
      (selectedProximalPoint_feasible B.prox θ.G_pos hR hn (L.point s.1))

theorem stage_state_invariant (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R)
    (t : ℕ) (history : AdaptiveKernel.History PUnit E t) :
    B.stageStateInvariant (((B.stageRule hR hn τ L).state (stageInitial L) n t history).2) := by
  induction t with
  | zero => exact ⟨fun _ => rfl, fun h => (Nat.not_lt_zero _ h).elim⟩
  | succ t ih =>
      simp only [CappedRaw.Rule.state, CappedRaw.Rule.step]
      split_ifs
      · exact B.stage_update_invariant hR hn τ L _ history.2 (ih history.1)
      · exact ih history.1

theorem stage_state_counts (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R)
    (t : ℕ) (history : AdaptiveKernel.History PUnit E t) :
    (((B.stageRule hR hn τ L).state (stageInitial L) n t history).2).2.2 =
      ((B.stageRule hR hn τ L).state (stageInitial L) n t history).1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [CappedRaw.Rule.state, CappedRaw.Rule.step]
      split_ifs
      · change _ + 1 = _ + 1
        exact congrArg (fun k : ℕ => k + 1) (ih history.1)
      · exact ih history.1

theorem stage_output_eq_average (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (T : ℕ)
    (history : AdaptiveKernel.History PUnit E T)
    (hsuccess : n ≤ ((B.stageRule hR hn τ L).state (stageInitial L) n T history).1) :
    ((B.cappedStagePolicy hR hn τ L T).output history : E) =
      stageAverage (((B.stageRule hR hn τ L).state (stageInitial L) n T history).2) := by
  have hc := B.stage_state_counts hR hn τ L T history
  have hi := B.stage_state_invariant hR hn τ L T history
  have hp : 0 < (((B.stageRule hR hn τ L).state (stageInitial L) n T history).2).2.2 := by omega
  change B.stageReadoutValue n _ = _
  exact if_pos ⟨by omega, hi.2 hp⟩

theorem stage_output_eq_fallback (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (T : ℕ)
    (history : AdaptiveKernel.History PUnit E T)
    (hfailure : ((B.stageRule hR hn τ L).state (stageInitial L) n T history).1 < n) :
    ((B.cappedStagePolicy hR hn τ L T).output history : E) = B.stageFallback := by
  have hc := B.stage_state_counts hR hn τ L T history
  change B.stageReadoutValue n _ = _
  apply if_neg
  intro h
  omega

def stageObjectiveIncrement (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (F : E → ℝ)
    (t : ℕ) (h : AdaptiveKernel.History PUnit E t × E) : ℝ :=
  let M := B.stageRule hR hn τ L
  let s := M.state (stageInitial L) n t h.1
  if (s, h.2) ∈ M.activeAcceptance n then
    F (selectedProximalPoint B.prox θ.G_pos hR hn (L.point s.2.1)) else 0

theorem stage_average_jensen (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R)
    {F : E → ℝ} (hF : ConvexOn ℝ B.S F) (t : ℕ)
    (history : AdaptiveKernel.History PUnit E t) :
    let s := ((B.stageRule hR hn τ L).state (stageInitial L) n t history).2
    (s.2.2 : ℝ) * F (stageAverage s) ≤
      AdaptiveKernel.historySum (B.stageObjectiveIncrement hR hn τ L F) t history := by
  induction t with
  | zero => simp [CappedRaw.Rule.state, stageInitial, AdaptiveKernel.historySum]
  | succ t ih =>
      let M := B.stageRule hR hn τ L
      let s := M.state (stageInitial L) n t history.1
      have hi := B.stage_state_invariant hR hn τ L t history.1
      have hj := runningAverage_next_convex_bound hF hi.1 hi.2
        (selectedProximalPoint_feasible B.prox θ.G_pos hR hn (L.point s.2.1))
      have hp := ih history.1
      change (((M.step n (s, history.2)).2.2.2 : ℕ) : ℝ) *
        F (stageAverage (M.step n (s, history.2)).2) ≤ _
      simp only [AdaptiveKernel.historySum, stageObjectiveIncrement]
      change _ ≤ AdaptiveKernel.historySum (B.stageObjectiveIncrement hR hn τ L F) t history.1 +
        (if (s, history.2) ∈ M.activeAcceptance n then
          F (selectedProximalPoint B.prox θ.G_pos hR hn (L.point s.2.1)) else 0)
      by_cases ha : (s, history.2) ∈ M.activeAcceptance n
      · simp only [CappedRaw.Rule.step, if_pos ha]
        change ((s.2.2.2 + 1 : ℕ) : ℝ) *
          F (runningAverage (s.2.2.2 + 1)
            (s.2.2.1 + selectedProximalPoint B.prox θ.G_pos hR hn (L.point s.2.1))) ≤ _
        push_cast
        exact hj.trans (add_le_add_right hp _)
      · simp only [CappedRaw.Rule.step, if_neg ha, add_zero]
        exact hp

end HeavyTail.PublicProblem
