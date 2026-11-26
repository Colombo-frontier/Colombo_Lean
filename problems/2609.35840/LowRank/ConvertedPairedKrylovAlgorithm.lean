import LowRank.PairedKrylovContinuation
import LowRank.RefinedPairedKrylovAlgorithm
import LowRank.TransposeOutputConversion

/-! Run the paired algorithm in the opposite orientation and query its
left output under A-transpose. This returns a right output for k extra calls. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def convertedPairedKrylovPolicy (a b k s t n r : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ)
      (pairedKrylovContinuationBudget s t (0 + k) n r) (PairedKrylovSeed a s t) :=
  pairedKrylovBlockContinuation a b s t (0 + k) n r
    (rectangularTransposeBlock a b k 0
      ⟨fun x => refinedPairedKrylovOutput b a k s t n r hkb hka x.2,
        (measurable_refinedPairedKrylovOutput b a k s t n r hkb hka).comp measurable_snd⟩
      ⟨fun x => completeOrthonormalColumns b k hkb x.2,
        (measurable_completeOrthonormalColumns b k hkb).comp measurable_snd⟩)

theorem convertedPairedKrylovPolicy_run {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    runBoundedRectangular a b (pairedKrylovContinuationBudget s t (0 + k) n r)
      (convertedPairedKrylovPolicy a b k s t n r hka hkb) A U =
        completeOrthonormalColumns b k hkb (Aᵀ *
          runBoundedRectangular b a (pairedKrylovQueryBudget s t n r)
            (refinedPairedKrylovPolicy b a k s t n r hkb hka) Aᵀ U) := by
  rw [convertedPairedKrylovPolicy, pairedKrylovBlockContinuation_run,
    rectangularTransposeBlock_run, refinedPairedKrylovPolicy_run]
  simp only [Matrix.transpose_transpose]
  change completeOrthonormalColumns b k hkb (Aᵀ * refinedRitzColumns b a k hkb hka
    (pairedKrylovCompressedMatrix (krylovBlockData A n U.1, krylovBlockData A r U.2))) = _
  rw [pairedKrylovCompressedMatrix_eq]

theorem convertedPairedKrylovPolicy_calls {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    ((convertedPairedKrylovPolicy a b k s t n r hka hkb).toProgram a b
      (pairedKrylovContinuationBudget s t (0 + k) n r) U).calls (rectangularOracle A) =
        k + 2 * s * n + 2 * t * r := by
  rw [convertedPairedKrylovPolicy, pairedKrylovBlockContinuation_calls, rectangularTransposeBlock_calls]
  simp only [BoundedRectangularPolicy.toProgram, OracleProgram.calls, Nat.zero_add]

theorem convertedPairedKrylovPolicy_orthogonal {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    let Z := runBoundedRectangular a b (pairedKrylovContinuationBudget s t (0 + k) n r)
      (convertedPairedKrylovPolicy a b k s t n r hka hkb) A U
    Zᵀ * Z = 1 := by
  dsimp only
  rw [convertedPairedKrylovPolicy_run]
  exact completeOrthonormalColumns_orthogonal hkb _

def convertedPairedKrylovAlgorithm (a b k s t n r : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (pairedKrylovContinuationBudget s t (0 + k) n r) where
  Seed := ULift.{u} (PairedKrylovSeed a s t)
  measurableSeed := inferInstance
  law := ((iidMatrixLaw a s 1).prod (iidMatrixLaw a t 1)).map ULift.up
  probability := inferInstance
  policy := (convertedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b
    (pairedKrylovContinuationBudget s t (0 + k) n r) ⟨ULift.down, measurable_down⟩
  orthonormal := by
    intro A seed
    dsimp only
    rw [runBoundedRectangular_mapState]
    exact convertedPairedKrylovPolicy_orthogonal hka hkb A seed.down

theorem convertedPairedKrylovAlgorithm_calls {a b k s t n r : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ)
    (seed : (convertedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).Seed) :
    ((convertedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy.toProgram a b
      (pairedKrylovContinuationBudget s t (0 + k) n r) seed).calls (rectangularOracle A) =
        k + 2 * s * n + 2 * t * r := by
  change (((convertedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b
    (pairedKrylovContinuationBudget s t (0 + k) n r) ⟨ULift.down, measurable_down⟩).toProgram a b
      (pairedKrylovContinuationBudget s t (0 + k) n r) seed).calls _ = _
  rw [BoundedRectangularPolicy.calls_mapState, convertedPairedKrylovPolicy_calls]

theorem convertedPairedKrylovAlgorithm_success_probability_ge {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) {p ε : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    (refinedPairedKrylovAlgorithm.{u} b a k s t n r hkb hka).law.real
      (rectangularSchattenSuccess p ε (refinedPairedKrylovAlgorithm.{u} b a k s t n r hkb hka).policy Aᵀ) ≤
        (convertedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).law.real
          (rectangularSchattenSuccess p ε (convertedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy A) := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro seed hseed
  change schattenNorm p (A * (1 -
    runBoundedRectangular a b (pairedKrylovContinuationBudget s t (0 + k) n r)
      ((convertedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b
        (pairedKrylovContinuationBudget s t (0 + k) n r) ⟨ULift.down, measurable_down⟩) A seed *
    (runBoundedRectangular a b (pairedKrylovContinuationBudget s t (0 + k) n r)
      ((convertedPairedKrylovPolicy a b k s t n r hka hkb).mapState a b
        (pairedKrylovContinuationBudget s t (0 + k) n r) ⟨ULift.down, measurable_down⟩) A seed)ᵀ)) ≤ _
  rw [runBoundedRectangular_mapState, convertedPairedKrylovPolicy_run]
  apply completeTransposeImage_relative hka hkb A _ hp
  change schattenNorm p (Aᵀ * (1 -
    runBoundedRectangular b a (pairedKrylovQueryBudget s t n r)
      ((refinedPairedKrylovPolicy b a k s t n r hkb hka).mapState b a
        (pairedKrylovQueryBudget s t n r) ⟨ULift.down, measurable_down⟩) Aᵀ seed *
    (runBoundedRectangular b a (pairedKrylovQueryBudget s t n r)
      ((refinedPairedKrylovPolicy b a k s t n r hkb hka).mapState b a
        (pairedKrylovQueryBudget s t n r) ⟨ULift.down, measurable_down⟩) Aᵀ seed)ᵀ)) ≤ _ at hseed
  rwa [runBoundedRectangular_mapState] at hseed

end
end LowRank
