import LowRank.PairedKrylovCompression
import LowRank.RefinedKrylovAlgorithm

/-! A single randomized algorithm combines both transposed Krylov spaces,
then refines the compressed spectral columns. Queries are exactly additive. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def refinedPairedKrylovOutput (a b k s t n r : ℕ) (hka : k ≤ a) (hkb : k ≤ b)
    (data : PairedKrylovData b a s t n r) : Matrix (Fin b) (Fin k) ℝ :=
  refinedRitzColumns a b k hka hkb (pairedKrylovCompressedMatrix data)

theorem measurable_refinedPairedKrylovOutput (a b k s t n r : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    Measurable (refinedPairedKrylovOutput a b k s t n r hka hkb) :=
  (measurable_refinedRitzColumns a b k hka hkb).comp
    (measurable_pairedKrylovCompressedMatrix b a s t n r)

def refinedPairedKrylovPolicy (a b k s t n r : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ)
      (pairedKrylovQueryBudget s t n r) (PairedKrylovSeed b s t) :=
  ((pairedKrylovBlockPolicy b a s t n r).transpose a b (pairedKrylovQueryBudget s t n r)).mapOutput a b
    ⟨refinedPairedKrylovOutput a b k s t n r hka hkb,
      measurable_refinedPairedKrylovOutput a b k s t n r hka hkb⟩ (pairedKrylovQueryBudget s t n r)

theorem refinedPairedKrylovPolicy_run {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed b s t) :
    runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U =
        refinedRitzColumns a b k hka hkb (Aᵀ * pairedKrylovProjector Aᵀ n r U) := by
  rw [refinedPairedKrylovPolicy, runBoundedRectangular_mapOutput,
    runBoundedRectangular_transpose, pairedKrylovBlockPolicy_run]
  exact congrArg (refinedRitzColumns a b k hka hkb) (pairedKrylovCompressedMatrix_eq Aᵀ U)

theorem refinedPairedKrylovPolicy_calls {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed b s t) :
    ((refinedPairedKrylovPolicy a b k s t n r hka hkb).toProgram a b
      (pairedKrylovQueryBudget s t n r) U).calls (rectangularOracle A) = 2 * s * n + 2 * t * r := by
  rw [refinedPairedKrylovPolicy, BoundedRectangularPolicy.calls_mapOutput,
    BoundedRectangularPolicy.calls_transpose, pairedKrylovBlockPolicy_calls]

theorem refinedPairedKrylovPolicy_orthogonal {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed b s t) :
    let Z := runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U
    Zᵀ * Z = 1 := by
  dsimp only
  rw [refinedPairedKrylovPolicy_run]
  exact refinedRitzColumns_orthogonal hka hkb _

def refinedPairedKrylovAlgorithm (a b k s t n r : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (pairedKrylovQueryBudget s t n r) where
  Seed := ULift.{u} (PairedKrylovSeed b s t)
  measurableSeed := inferInstance
  law := ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)).map ULift.up
  probability := inferInstance
  policy := (refinedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b (pairedKrylovQueryBudget s t n r)
    ⟨ULift.down, measurable_down⟩
  orthonormal := by
    intro A seed
    dsimp only
    rw [runBoundedRectangular_mapState]
    exact refinedPairedKrylovPolicy_orthogonal hka hkb A seed.down

theorem refinedPairedKrylovAlgorithm_calls {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ)
    (seed : (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).Seed) :
    ((refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy.toProgram a b
      (pairedKrylovQueryBudget s t n r) seed).calls (rectangularOracle A) = 2 * s * n + 2 * t * r := by
  change (((refinedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b (pairedKrylovQueryBudget s t n r)
    ⟨ULift.down, measurable_down⟩).toProgram a b (pairedKrylovQueryBudget s t n r) seed).calls _ = _
  rw [BoundedRectangularPolicy.calls_mapState, refinedPairedKrylovPolicy_calls]

theorem refinedPairedKrylovAlgorithm_success_probability {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) {p : ℝ} (hp : 0 < p) (ε : ℝ)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).law.real
      (rectangularSchattenSuccess p ε (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy A) =
        ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)).real
          (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A) := by
  have hset : rectangularSchattenSuccess p ε
      (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy A =
        ULift.down ⁻¹' rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A := by
    ext seed
    simp only [rectangularSchattenSuccess, Set.mem_setOf_eq, Set.mem_preimage]
    change schattenNorm p (A * (1 -
      runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
        ((refinedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b (pairedKrylovQueryBudget s t n r)
          ⟨ULift.down, measurable_down⟩) A seed *
      (runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
        ((refinedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b (pairedKrylovQueryBudget s t n r)
          ⟨ULift.down, measurable_down⟩) A seed)ᵀ)) ≤ _ ↔ _
    rw [runBoundedRectangular_mapState]
  rw [hset]
  change (((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)).map ULift.up).real (ULift.down ⁻¹' _) = _
  rw [Measure.real, Measure.map_apply measurable_up
    ((measurableSet_rectangularSchattenSuccess hkb hp ε _ A).preimage measurable_down)]
  rfl

end
end LowRank
