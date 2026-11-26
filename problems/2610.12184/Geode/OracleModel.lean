import Geode.GeodesicConvex
import Geode.Subgradient
import Geode.OracleReplay
import Geode.Parameters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENNReal.Real

/-! The actual deterministic first-order model and dimension-uniform minimax
query complexity. These are specifications, not assumed complexity bounds. -/
namespace Geode.Lorentz

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure AdmissibleObjective (o : Point E) (R L : ℝ) (f : Point E → ℝ) : Prop where
  convex : GConvexFunction f
  lipschitz : ∀ x y, |f x - f y| ≤ L * dist x y
  minimizer : ∃ p, dist o p ≤ R ∧ ∀ y, f p ≤ f y

abbrev FirstOrderReply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℝ × Ambient E

def LegalOracle (f : Point E → ℝ) (O : Point E → FirstOrderReply E) : Prop :=
  ∀ x, (O x).1 = f x ∧ IsSubgradient f x (O x).2

abbrev FirstOrderAlgorithm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  Geode.OracleReplay.StoppingAlgorithm (Point E) (FirstOrderReply E)

def Guarantees (o : Point E) (R L ε : ℝ) (N : ℕ) (A : FirstOrderAlgorithm E) : Prop :=
  ∀ f : Point E → ℝ, AdmissibleObjective o R L f →
    ∀ O : Point E → FirstOrderReply E, LegalOracle f O →
      ∃ history output,
        Geode.OracleReplay.run A (Geode.OracleReplay.fixedResponder O) N [] =
          .finished history output ∧
        ∀ p : Point E, (∀ y, f p ≤ f y) → f output - f p ≤ ε * L * R

def FeasibleBudget (o : Point E) (R L ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : FirstOrderAlgorithm E, Guarantees o R L ε N A

/-- Infimum over actual feasible finite budgets; empty feasible sets give ∞. -/
noncomputable def queryComplexity (o : Point E) (R L ε : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : FeasibleBudget o R L ε N), (N : ℝ≥0∞)

theorem queryComplexity_le_of_feasible {o : Point E} {R L ε : ℝ} {N : ℕ}
    (h : FeasibleBudget o R L ε N) : queryComplexity o R L ε ≤ (N : ℝ≥0∞) :=
  iInf_le_of_le N (iInf_le_of_le h le_rfl)

theorem queryComplexity_lower_of_no_budget {o : Point E} {R L ε : ℝ} {T : ℕ}
    (h : ∀ N ≤ T, ¬ FeasibleBudget o R L ε N) :
    ((T + 1 : ℕ) : ℝ≥0∞) ≤ queryComplexity o R L ε := by
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  have hlt : T < N := by
    by_contra hn
    exact h N (Nat.le_of_not_gt hn) hN
  exact_mod_cast Nat.succ_le_of_lt hlt

abbrev HyperbolicSpace (d : ℕ) := Point (EuclideanSpace ℝ (Fin d))

noncomputable def dimensionComplexity (d : ℕ) (R L ε : ℝ) : ℝ≥0∞ :=
  queryComplexity (origin : HyperbolicSpace d) R L ε

noncomputable def uniformComplexity (R L ε : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 2 ≤ d), dimensionComplexity d R L ε

theorem dimensionComplexity_le_uniform {d : ℕ} (hd : 2 ≤ d) (R L ε : ℝ) :
    dimensionComplexity d R L ε ≤ uniformComplexity R L ε :=
  le_iSup_of_le d (le_iSup_of_le hd le_rfl)

theorem uniformComplexity_le_of_dimensions {R L ε : ℝ} {B : ℝ≥0∞}
    (h : ∀ d, 2 ≤ d → dimensionComplexity d R L ε ≤ B) :
    uniformComplexity R L ε ≤ B := iSup_le (fun d => iSup_le (h d))

/-- Exact main-bound target, proved by `matchingComplexityStatement_verified`
in `Geode.Main`. -/
def MatchingComplexityStatement : Prop :=
  ∀ R L ε : ℝ, 0 < R → 0 < L → 0 < ε → ε ≤ 1 / 64 →
    ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤ uniformComplexity R L ε ∧
    uniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞)

end Geode.Lorentz
