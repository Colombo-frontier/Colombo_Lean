import LowRank.ExactMatrixQueries
import LowRank.MeasurableOptimalColumns
import LowRank.RectangularOutputMap
import LowRank.RectangularQueryComplexity

/-! A deterministic measurable algorithm reads the matrix using min(a,b)
products and returns an exact optimal rank-k right subspace. This proves
the saturation upper bound in the manuscript's actual minimax model. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

def exactColumnPolicy (a b k : ℕ) (hk : k ≤ b) (S : Type u) [MeasurableSpace S] :
    BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) (min a b) S :=
  (exactMatrixPolicy a b S).mapOutput a b
    ⟨optimalColumnSelector a b k hk, measurable_optimalColumnSelector a b k hk⟩ (min a b)

theorem exactColumnPolicy_run (a b k : ℕ) (hk : k ≤ b) {S : Type u} [MeasurableSpace S]
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b (min a b) (exactColumnPolicy a b k hk S) A seed =
      optimalColumnSelector a b k hk A := by
  rw [exactColumnPolicy, runBoundedRectangular_mapOutput, exactMatrixPolicy_run]

theorem exactColumnPolicy_calls (a b k : ℕ) (hk : k ≤ b) {S : Type u} [MeasurableSpace S]
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((exactColumnPolicy a b k hk S).toProgram a b (min a b) seed).calls (rectangularOracle A) = min a b := by
  rw [exactColumnPolicy, BoundedRectangularPolicy.calls_mapOutput, exactMatrixPolicy_calls]

def exactColumnAlgorithm (a b k : ℕ) (hk : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (min a b) where
  Seed := PUnit.{u + 1}
  measurableSeed := inferInstance
  law := Measure.dirac PUnit.unit
  probability := inferInstance
  policy := exactColumnPolicy a b k hk PUnit
  orthonormal := by
    intro A seed
    dsimp only
    rw [exactColumnPolicy_run]
    exact optimalColumnSelector_orthogonal hk A

theorem exactColumnAlgorithm_optimal {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : (exactColumnAlgorithm.{u} a b k hk).Seed)
    {p : ℝ} (hp : 0 < p) :
    let Z := runBoundedRectangular a b (min a b) (exactColumnAlgorithm.{u} a b k hk).policy A seed
    schattenNorm p (A * (1 - Z * Zᵀ)) = optimalSchattenNorm p A k := by
  change schattenNorm p (A * (1 -
    runBoundedRectangular a b (min a b) (exactColumnPolicy a b k hk PUnit) A seed *
      (runBoundedRectangular a b (min a b) (exactColumnPolicy a b k hk PUnit) A seed)ᵀ)) = _
  rw [exactColumnPolicy_run]
  exact optimalColumnSelector_residual hk A hp

theorem exactColumnAlgorithm_succeeds {a b k : ℕ} (hk : k ≤ b)
    {p ε δ : ℝ} (hp : 0 < p) (hε : 0 ≤ ε) (hδ : δ ≤ 1) :
    (exactColumnAlgorithm.{u} a b k hk).Succeeds p ε δ := by
  intro A
  have hnonneg : 0 ≤ optimalSchattenNorm p A k := by
    obtain ⟨P, _, _, heq⟩ := (optimalSchattenNorm_isLeast_rankBounded hp A hk).1
    rw [heq]
    exact schattenNorm_nonneg _ _
  have huniv : rectangularSchattenSuccess p ε (exactColumnAlgorithm.{u} a b k hk).policy A = Set.univ := by
    ext seed
    simp only [Set.mem_univ, iff_true]
    change schattenNorm p (A * (1 -
      runBoundedRectangular a b (min a b) (exactColumnAlgorithm.{u} a b k hk).policy A seed *
        (runBoundedRectangular a b (min a b) (exactColumnAlgorithm.{u} a b k hk).policy A seed)ᵀ)) ≤ _
    rw [exactColumnAlgorithm_optimal hk A seed hp]
    nlinarith
  rw [huniv, measureReal_univ_eq_one]
  exact hδ

theorem rectangularQueryComplexity_le_dimension {a b k : ℕ} (hk : k ≤ b)
    {p ε δ : ℝ} (hp : 0 < p) (hε : 0 ≤ ε) (hδ : δ ≤ 1) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤ ((min a b : ℕ) : ℝ≥0∞) :=
  rectangularQueryComplexity_le_budget (exactColumnAlgorithm.{u} a b k hk)
    (exactColumnAlgorithm_succeeds hk hp hε hδ)

end
end LowRank
