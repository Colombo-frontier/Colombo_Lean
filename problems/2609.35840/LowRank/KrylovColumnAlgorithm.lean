import LowRank.KrylovCompression
import LowRank.MeasurableOptimalColumns
import LowRank.RectangularOutputMap
import LowRank.RectangularQueryComplexity

/-! A genuine randomized, measurable column-output algorithm built from
block Krylov queries and spectral postprocessing of the restricted operator.
The seed is an input-independent iid standard Gaussian matrix. Its query
cost and orthonormal output are proved; convergence rates are separate. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def krylovColumnOutput (a b k s n : ℕ) (hk : k ≤ b)
    (data : Fin n → KrylovBlockPair a b s) : Matrix (Fin b) (Fin k) ℝ :=
  optimalColumnSelector a b k hk (krylovCompressedMatrix data)

theorem measurable_krylovColumnOutput (a b k s n : ℕ) (hk : k ≤ b) :
    Measurable (krylovColumnOutput a b k s n hk) :=
  (measurable_optimalColumnSelector a b k hk).comp (measurable_krylovCompressedMatrix a b s n)

theorem krylovColumnOutput_orthogonal {a b k s n : ℕ} (hk : k ≤ b)
    (data : Fin n → KrylovBlockPair a b s) :
    (krylovColumnOutput a b k s n hk data)ᵀ * krylovColumnOutput a b k s n hk data = 1 :=
  optimalColumnSelector_orthogonal hk _

def krylovColumnPolicy (a b k s n : ℕ) (hk : k ≤ b) :
    BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ)
      (krylovQueryBudget s 0 n) (Matrix (Fin a) (Fin s) ℝ) :=
  (krylovBlockPolicy a b s n).mapOutput a b
    ⟨krylovColumnOutput a b k s n hk, measurable_krylovColumnOutput a b k s n hk⟩
    (krylovQueryBudget s 0 n)

theorem krylovColumnPolicy_run {a b k s n : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) :
    runBoundedRectangular a b (krylovQueryBudget s 0 n) (krylovColumnPolicy a b k s n hk) A U =
      optimalColumnSelector a b k hk
        (A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) := by
  rw [krylovColumnPolicy, runBoundedRectangular_mapOutput, krylovBlockPolicy_run]
  exact congrArg (optimalColumnSelector a b k hk) (krylovCompressedMatrix_eq A U)

theorem krylovColumnPolicy_calls {a b k s n : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) :
    ((krylovColumnPolicy a b k s n hk).toProgram a b (krylovQueryBudget s 0 n) U).calls
      (rectangularOracle A) = 2 * s * n := by
  rw [krylovColumnPolicy, BoundedRectangularPolicy.calls_mapOutput, krylovBlockPolicy_calls]

theorem krylovColumnPolicy_orthogonal {a b k s n : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) :
    let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (krylovColumnPolicy a b k s n hk) A U
    Zᵀ * Z = 1 := by
  dsimp only
  rw [krylovColumnPolicy_run]
  exact optimalColumnSelector_orthogonal hk _

theorem krylovColumnPolicy_optimal_of_spans {a b k s n : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ)
    (hspan : A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) = A)
    {p : ℝ} (hp : 0 < p) :
    let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (krylovColumnPolicy a b k s n hk) A U
    schattenNorm p (A * (1 - Z * Zᵀ)) = optimalSchattenNorm p A k := by
  dsimp only
  rw [krylovColumnPolicy_run, hspan]
  exact optimalColumnSelector_residual hk A hp

def krylovColumnAlgorithm (a b k s n : ℕ) (hk : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (krylovQueryBudget s 0 n) where
  Seed := ULift.{u} (Matrix (Fin a) (Fin s) ℝ)
  measurableSeed := inferInstance
  law := (iidMatrixLaw a s 1).map ULift.up
  probability := inferInstance
  policy := (krylovColumnPolicy a b k s n hk).mapState a b (krylovQueryBudget s 0 n)
    ⟨ULift.down, measurable_down⟩
  orthonormal := by
    intro A seed
    dsimp only
    rw [runBoundedRectangular_mapState]
    exact krylovColumnPolicy_orthogonal hk A seed.down

theorem krylovColumnAlgorithm_calls {a b k s n : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : (krylovColumnAlgorithm.{u} a b k s n hk).Seed) :
    ((krylovColumnAlgorithm.{u} a b k s n hk).policy.toProgram a b
      (krylovQueryBudget s 0 n) seed).calls (rectangularOracle A) = 2 * s * n := by
  change (((krylovColumnPolicy a b k s n hk).mapState a b (krylovQueryBudget s 0 n)
    ⟨ULift.down, measurable_down⟩).toProgram a b (krylovQueryBudget s 0 n) seed).calls _ = _
  rw [BoundedRectangularPolicy.calls_mapState, krylovColumnPolicy_calls]

theorem krylovColumnAlgorithm_success_probability {a b k s n : ℕ} (hk : k ≤ b)
    {p : ℝ} (hp : 0 < p) (ε : ℝ) (A : Matrix (Fin a) (Fin b) ℝ) :
    (krylovColumnAlgorithm.{u} a b k s n hk).law.real
        (rectangularSchattenSuccess p ε (krylovColumnAlgorithm.{u} a b k s n hk).policy A) =
      (iidMatrixLaw a s 1).real (rectangularSchattenSuccess p ε (krylovColumnPolicy a b k s n hk) A) := by
  have hset : rectangularSchattenSuccess p ε (krylovColumnAlgorithm.{u} a b k s n hk).policy A =
      ULift.down ⁻¹' rectangularSchattenSuccess p ε (krylovColumnPolicy a b k s n hk) A := by
    ext seed
    simp only [rectangularSchattenSuccess, Set.mem_setOf_eq, Set.mem_preimage]
    change schattenNorm p (A * (1 -
      runBoundedRectangular a b (krylovQueryBudget s 0 n)
        ((krylovColumnPolicy a b k s n hk).mapState a b (krylovQueryBudget s 0 n)
          ⟨ULift.down, measurable_down⟩) A seed *
      (runBoundedRectangular a b (krylovQueryBudget s 0 n)
        ((krylovColumnPolicy a b k s n hk).mapState a b (krylovQueryBudget s 0 n)
          ⟨ULift.down, measurable_down⟩) A seed)ᵀ)) ≤ _ ↔ _
    rw [runBoundedRectangular_mapState]
  rw [hset]
  change ((iidMatrixLaw a s 1).map ULift.up).real (ULift.down ⁻¹' _) = _
  rw [Measure.real, Measure.map_apply measurable_up
    ((measurableSet_rectangularSchattenSuccess hk hp ε _ A).preimage measurable_down)]
  rfl

end
end LowRank
