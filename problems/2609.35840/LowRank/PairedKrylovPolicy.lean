import LowRank.KrylovBlockPolicy

/-! Two Krylov runs of different block widths and lengths, using one actual
oracle policy. Both transcripts are retained and their costs add exactly. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

abbrev PairedKrylovSeed (a s t : ℕ) :=
  Matrix (Fin a) (Fin s) ℝ × Matrix (Fin a) (Fin t) ℝ

abbrev PairedKrylovData (a b s t n r : ℕ) :=
  (Fin n → KrylovBlockPair a b s) × (Fin r → KrylovBlockPair a b t)

def pairedKrylovQueryBudget (s t n r : ℕ) : ℕ :=
  krylovQueryBudget s (krylovQueryBudget t 0 r) n

theorem pairedKrylovQueryBudget_eq (s t n r : ℕ) :
    pairedKrylovQueryBudget s t n r = 2 * s * n + 2 * t * r := by
  simp only [pairedKrylovQueryBudget, krylovQueryBudget_eq]
  omega

def pairedKrylovBlockPolicy (a b s t n r : ℕ) :
    BoundedRectangularPolicy a b (PairedKrylovData a b s t n r)
      (pairedKrylovQueryBudget s t n r) (PairedKrylovSeed a s t) :=
  krylovBlockContinuation a b s (krylovQueryBudget t 0 r) n
    ⟨Prod.fst, measurable_fst⟩
    (krylovBlockContinuation a b t 0 r
      ⟨fun x => x.1.2, measurable_fst.snd⟩
      ⟨fun x => (x.1.2, x.2), measurable_fst.snd.prodMk measurable_snd⟩)

theorem pairedKrylovBlockPolicy_run {a b s t n r : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (pairedKrylovBlockPolicy a b s t n r) A U =
        (krylovBlockData A n U.1, krylovBlockData A r U.2) := by
  change runBoundedRectangular a b (krylovQueryBudget s (krylovQueryBudget t 0 r) n) _ A U = _
  rw [pairedKrylovBlockPolicy, krylovBlockContinuation_run, krylovBlockContinuation_run]
  rfl

theorem pairedKrylovBlockPolicy_calls {a b s t n r : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : PairedKrylovSeed a s t) :
    ((pairedKrylovBlockPolicy a b s t n r).toProgram a b
      (pairedKrylovQueryBudget s t n r) U).calls (rectangularOracle A) =
        2 * s * n + 2 * t * r := by
  change (BoundedRectangularPolicy.toProgram a b (krylovQueryBudget s (krylovQueryBudget t 0 r) n)
    _ U).calls (rectangularOracle A) = _
  rw [pairedKrylovBlockPolicy, krylovBlockContinuation_calls, krylovBlockContinuation_calls]
  simp only [BoundedRectangularPolicy.toProgram, OracleProgram.calls]
  omega

end
end LowRank
