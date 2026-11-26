import NCConcave16991.SmoothProblemEmbedding
import NCConcave16991.UpperAssembly

/-! # The uniform randomized oracle reduction in Appendix F.1

The smooth oracle is represented by the singleton-dual policy interface. Its
reply is exactly the component value, its gradient, and the unique zero vector.
Thus the embedding uses one original query per query and keeps arbitrary
private seed laws, stopping rules, and output points. The external smooth
lower-bound theorem itself is not assumed or asserted here.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991

def SmoothDirectSuccess {p : ProblemParameters} {dx : ℕ}
    (A : RandomizedPolicy (smoothDualDomain p) (n := p.n) (dx := dx))
    (F : SmoothFiniteSum p dx) (budget : ℕ) (η : ℝ) : Prop :=
  letI : MeasurableSpace A.Seed := A.seedSpace
  let event := {seed | ‖gradient (smoothSumAverage F.component)
    (randomizedOutput A F.toProblem budget seed)‖ ≤ η}
  MeasurableSet event ∧ (2 / 3 : ℝ≥0∞) ≤ A.law event

def SmoothDirectValidBudget (p : ProblemParameters) (η : ℝ) (budget : ℕ) : Prop :=
  ∀ (dx : ℕ) (x0 : PrimalSpace dx),
    ∃ A : RandomizedPolicy (smoothDualDomain p) (n := p.n) (dx := dx),
      ∀ F : SmoothFiniteSum p dx, F.initialPoint = x0 → SmoothDirectSuccess A F budget η

namespace SmoothFiniteSum

variable {p : ProblemParameters} {dx : ℕ}

theorem average_gradient_continuous (F : SmoothFiniteSum p dx) :
    Continuous (gradient (smoothSumAverage F.component)) := by
  have hL : LipschitzWith ⟨p.L, p.L_pos.le⟩ (averageMap F.componentGradient) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (averageMap F.componentGradient x) (averageMap F.componentGradient y) ≤ p.L * dist x y
    simpa only [dist_eq_norm] using F.averageGradient_lipschitz x y
  have he : gradient (smoothSumAverage F.component) = averageMap F.componentGradient :=
    funext (fun x ↦ (F.average_hasGradientAt x).gradient)
  rw [he]
  exact hL.continuous

theorem success_implies_direct (F : SmoothFiniteSum p dx)
    (A : RandomizedPolicy (smoothDualDomain p) (n := p.n) (dx := dx))
    (budget : ℕ) (h : Success A F.toProblem budget) :
    SmoothDirectSuccess A F budget ((3 / 2 : ℝ) * p.epsilon) := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  have hm := F.average_gradient_continuous.measurable.comp
    (randomizedOutput_measurable A F.toProblem
      (F.toProblem.individual_implies_averaged F.toProblem_individualSmooth) budget)
  refine ⟨measurableSet_le hm.norm measurable_const, ?_⟩
  apply h.2.trans
  apply measure_mono
  intro seed hs
  exact F.stationary_implies_direct_gradient _ hs

end SmoothFiniteSum

theorem smoothDirectValidBudget_of_validBudget {p : ProblemParameters} {budget : ℕ}
    (h : ValidBudget p .individual budget) :
    SmoothDirectValidBudget p ((3 / 2 : ℝ) * p.epsilon) budget := by
  intro dx x0
  obtain ⟨A, hA⟩ := h dx 0 (smoothDualDomain p) x0
  refine ⟨A, ?_⟩
  intro F hF
  exact F.success_implies_direct A budget (hA F.toProblem hF F.toProblem_individualSmooth)

/-- Every proved smooth direct-gradient lower bound transfers with precisely
the factor 3/2 in the accuracy, the same fixed budget, and no new queries. -/
theorem lowerBudget_of_smoothDirect {p : ProblemParameters} {b : ℝ}
    (h : ∀ budget : ℕ, SmoothDirectValidBudget p ((3 / 2 : ℝ) * p.epsilon) budget →
      b ≤ (budget : ℝ)) : LowerBudgetBound p .individual b := by
  intro budget hbudget
  exact h budget (smoothDirectValidBudget_of_validBudget hbudget)

end NCConcave16991
