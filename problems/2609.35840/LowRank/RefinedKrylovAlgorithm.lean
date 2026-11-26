import LowRank.RectangularTransposePolicy
import LowRank.KrylovColumnAlgorithm
import LowRank.RefinedRitzResidual

/-! A measurable Gaussian Krylov algorithm using transposed block queries
and refined right columns. The output uses only the query transcript;
orthogonality and exact cost hold for every input and seed. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def refinedKrylovOutput (a b k s n : ℕ) (hka : k ≤ a) (hkb : k ≤ b)
    (data : Fin n → KrylovBlockPair b a s) : Matrix (Fin b) (Fin k) ℝ :=
  refinedRitzColumns a b k hka hkb (krylovCompressedMatrix data)

theorem measurable_refinedKrylovOutput (a b k s n : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    Measurable (refinedKrylovOutput a b k s n hka hkb) :=
  (measurable_refinedRitzColumns a b k hka hkb).comp (measurable_krylovCompressedMatrix b a s n)

def refinedKrylovPolicy (a b k s n : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ)
      (krylovQueryBudget s 0 n) (Matrix (Fin b) (Fin s) ℝ) :=
  ((krylovBlockPolicy b a s n).transpose a b (krylovQueryBudget s 0 n)).mapOutput a b
    ⟨refinedKrylovOutput a b k s n hka hkb,
      measurable_refinedKrylovOutput a b k s n hka hkb⟩ (krylovQueryBudget s 0 n)

theorem refinedKrylovPolicy_run {a b k s n : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin b) (Fin s) ℝ) :
    runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U =
        refinedRitzColumns a b k hka hkb
          (Aᵀ * columnRangeProjector (krylovRightBlocks (krylovBlockData Aᵀ n U))) := by
  rw [refinedKrylovPolicy, runBoundedRectangular_mapOutput,
    runBoundedRectangular_transpose, krylovBlockPolicy_run]
  exact congrArg (refinedRitzColumns a b k hka hkb) (krylovCompressedMatrix_eq Aᵀ U)

theorem refinedKrylovPolicy_calls {a b k s n : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin b) (Fin s) ℝ) :
    ((refinedKrylovPolicy a b k s n hka hkb).toProgram a b
      (krylovQueryBudget s 0 n) U).calls (rectangularOracle A) = 2 * s * n := by
  rw [refinedKrylovPolicy, BoundedRectangularPolicy.calls_mapOutput,
    BoundedRectangularPolicy.calls_transpose, krylovBlockPolicy_calls]

theorem refinedKrylovPolicy_orthogonal {a b k s n : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin b) (Fin s) ℝ) :
    let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U
    Zᵀ * Z = 1 := by
  dsimp only
  rw [refinedKrylovPolicy_run]
  exact refinedRitzColumns_orthogonal hka hkb _

def refinedKrylovAlgorithm (a b k s n : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (krylovQueryBudget s 0 n) where
  Seed := ULift.{u} (Matrix (Fin b) (Fin s) ℝ)
  measurableSeed := inferInstance
  law := (iidMatrixLaw b s 1).map ULift.up
  probability := inferInstance
  policy := (refinedKrylovPolicy a b k s n hka hkb).mapState a b (krylovQueryBudget s 0 n)
    ⟨ULift.down, measurable_down⟩
  orthonormal := by
    intro A seed
    dsimp only
    rw [runBoundedRectangular_mapState]
    exact refinedKrylovPolicy_orthogonal hka hkb A seed.down

theorem refinedKrylovAlgorithm_calls {a b k s n : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ)
    (seed : (refinedKrylovAlgorithm.{u} a b k s n hka hkb).Seed) :
    ((refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy.toProgram a b
      (krylovQueryBudget s 0 n) seed).calls (rectangularOracle A) = 2 * s * n := by
  change (((refinedKrylovPolicy a b k s n hka hkb).mapState a b (krylovQueryBudget s 0 n)
    ⟨ULift.down, measurable_down⟩).toProgram a b (krylovQueryBudget s 0 n) seed).calls _ = _
  rw [BoundedRectangularPolicy.calls_mapState, refinedKrylovPolicy_calls]

theorem refinedKrylovAlgorithm_success_probability {a b k s n : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) {p : ℝ} (hp : 0 < p) (ε : ℝ)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    (refinedKrylovAlgorithm.{u} a b k s n hka hkb).law.real
      (rectangularSchattenSuccess p ε (refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy A) =
        (iidMatrixLaw b s 1).real
          (rectangularSchattenSuccess p ε (refinedKrylovPolicy a b k s n hka hkb) A) := by
  have hset : rectangularSchattenSuccess p ε
      (refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy A =
        ULift.down ⁻¹' rectangularSchattenSuccess p ε (refinedKrylovPolicy a b k s n hka hkb) A := by
    ext seed
    simp only [rectangularSchattenSuccess, Set.mem_setOf_eq, Set.mem_preimage]
    change schattenNorm p (A * (1 -
      runBoundedRectangular a b (krylovQueryBudget s 0 n)
        ((refinedKrylovPolicy a b k s n hka hkb).mapState a b (krylovQueryBudget s 0 n)
          ⟨ULift.down, measurable_down⟩) A seed *
      (runBoundedRectangular a b (krylovQueryBudget s 0 n)
        ((refinedKrylovPolicy a b k s n hka hkb).mapState a b (krylovQueryBudget s 0 n)
          ⟨ULift.down, measurable_down⟩) A seed)ᵀ)) ≤ _ ↔ _
    rw [runBoundedRectangular_mapState]
  rw [hset]
  change ((iidMatrixLaw b s 1).map ULift.up).real (ULift.down ⁻¹' _) = _
  rw [Measure.real, Measure.map_apply measurable_up
    ((measurableSet_rectangularSchattenSuccess hkb hp ε _ A).preimage measurable_down)]
  rfl

end
end LowRank
