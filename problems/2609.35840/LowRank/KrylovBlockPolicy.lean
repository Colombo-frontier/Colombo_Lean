import LowRank.RectangularBlockQueries

/-! A measurable oracle implementation of block Krylov data. Each step
queries A-transpose on the current left block, then A on the resulting right
block. The stored pairs contain both K and A K, so subsequent compression
can be computed from the transcript. No approximation guarantee is asserted. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u v

abbrev KrylovBlockPair (a b s : ℕ) :=
  Matrix (Fin b) (Fin s) ℝ × Matrix (Fin a) (Fin s) ℝ

def krylovBlockData {a b s : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    (n : ℕ) → Matrix (Fin a) (Fin s) ℝ → Fin n → KrylovBlockPair a b s
  | 0, _ => Fin.elim0
  | n + 1, U => Fin.cons (Aᵀ * U, A * (Aᵀ * U)) (krylovBlockData A n (A * (Aᵀ * U)))

def krylovQueryBudget (s m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => krylovQueryBudget s m n + s + s

theorem krylovQueryBudget_eq (s m n : ℕ) : krylovQueryBudget s m n = m + 2 * s * n := by
  induction n with
  | zero => simp [krylovQueryBudget]
  | succ n ih => rw [krylovQueryBudget, ih]; ring

def krylovBlockContinuation (a b s m : ℕ) {O : Type v} [MeasurableSpace O] :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
      MeasurableStateMap S (Matrix (Fin a) (Fin s) ℝ) →
      BoundedRectangularPolicy a b O m (S × (Fin n → KrylovBlockPair a b s)) →
      BoundedRectangularPolicy a b O (krylovQueryBudget s m n) S
  | 0, _, _, _, next =>
      next.mapState a b m ⟨fun x => (x, Fin.elim0), measurable_id.prodMk measurable_const⟩
  | n + 1, S, _, block, next =>
      rectangularTransposeBlock a b s (krylovQueryBudget s m n + s) block
        (rectangularForwardBlock a b s (krylovQueryBudget s m n) ⟨Prod.snd, measurable_snd⟩
          (krylovBlockContinuation a b s m n ⟨Prod.snd, measurable_snd⟩
            (next.mapState a b m
              ⟨fun x => (x.1.1.1, Fin.cons (x.1.1.2, x.1.2) x.2),
                measurable_fst.fst.fst.prodMk
                  (measurable_fin_cons n
                    (fun x : ((S × Matrix (Fin b) (Fin s) ℝ) × Matrix (Fin a) (Fin s) ℝ) ×
                        (Fin n → KrylovBlockPair a b s) => (x.1.1.2, x.1.2))
                    (fun x => x.2) (measurable_fst.fst.snd.prodMk measurable_fst.snd)
                    measurable_snd)⟩)))

theorem krylovBlockContinuation_run (a b s m n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin a) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × (Fin n → KrylovBlockPair a b s)))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    runBoundedRectangular a b (krylovQueryBudget s m n)
        (krylovBlockContinuation a b s m n block next) A seed =
      runBoundedRectangular a b m next A (seed, krylovBlockData A n (block.1 seed)) := by
  induction n generalizing S with
  | zero =>
      change runBoundedRectangular a b m _ A seed = _
      rw [krylovBlockContinuation, runBoundedRectangular_mapState]
      rfl
  | succ n ih =>
      change runBoundedRectangular a b (krylovQueryBudget s m n + s + s) _ A seed = _
      rw [krylovBlockContinuation, rectangularTransposeBlock_run, rectangularForwardBlock_run,
        ih, runBoundedRectangular_mapState]
      rfl

theorem krylovBlockContinuation_calls (a b s m n : ℕ) {S : Type u} {O : Type v}
    [MeasurableSpace S] [MeasurableSpace O]
    (block : MeasurableStateMap S (Matrix (Fin a) (Fin s) ℝ))
    (next : BoundedRectangularPolicy a b O m (S × (Fin n → KrylovBlockPair a b s)))
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : S) :
    ((krylovBlockContinuation a b s m n block next).toProgram a b (krylovQueryBudget s m n) seed).calls
        (rectangularOracle A) =
      (next.toProgram a b m (seed, krylovBlockData A n (block.1 seed))).calls (rectangularOracle A) + 2 * s * n := by
  induction n generalizing S with
  | zero =>
      change (BoundedRectangularPolicy.toProgram a b m _ seed).calls (rectangularOracle A) = _
      rw [krylovBlockContinuation, BoundedRectangularPolicy.toProgram_mapState]
      simp only [krylovBlockData, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
      change (BoundedRectangularPolicy.toProgram a b (krylovQueryBudget s m n + s + s) _ seed).calls
        (rectangularOracle A) = _
      rw [krylovBlockContinuation, rectangularTransposeBlock_calls, rectangularForwardBlock_calls,
        ih, BoundedRectangularPolicy.toProgram_mapState]
      simp only [krylovBlockData]
      ring

def krylovBlockPolicy (a b s n : ℕ) :
    BoundedRectangularPolicy a b (Fin n → KrylovBlockPair a b s)
      (krylovQueryBudget s 0 n) (Matrix (Fin a) (Fin s) ℝ) :=
  krylovBlockContinuation a b s 0 n ⟨id, measurable_id⟩ ⟨Prod.snd, measurable_snd⟩

theorem krylovBlockPolicy_run {a b s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) :
    runBoundedRectangular a b (krylovQueryBudget s 0 n) (krylovBlockPolicy a b s n) A U =
      krylovBlockData A n U := by
  rw [krylovBlockPolicy, krylovBlockContinuation_run]
  rfl

theorem krylovBlockPolicy_calls {a b s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) :
    ((krylovBlockPolicy a b s n).toProgram a b (krylovQueryBudget s 0 n) U).calls
      (rectangularOracle A) = 2 * s * n := by
  rw [krylovBlockPolicy, krylovBlockContinuation_calls]
  simp only [BoundedRectangularPolicy.toProgram, OracleProgram.calls, Nat.zero_add]

theorem krylovBlockData_power {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (i : Fin n) :
    krylovBlockData A n U i =
      ((Aᵀ * A) ^ i.val * (Aᵀ * U), A * ((Aᵀ * A) ^ i.val * (Aᵀ * U))) := by
  induction n generalizing U with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [krylovBlockData]
      · simp only [krylovBlockData, Fin.cons_succ, ih, Fin.val_succ, pow_succ, Matrix.mul_assoc]

theorem measurable_krylovBlockData (a b s n : ℕ) :
    Measurable (fun x : Matrix (Fin a) (Fin b) ℝ × Matrix (Fin a) (Fin s) ℝ =>
      krylovBlockData x.1 n x.2) := by
  have hm := measurable_runBoundedRectangular a b (krylovQueryBudget s 0 n) (krylovBlockPolicy a b s n)
  simpa only [krylovBlockPolicy_run] using hm

end
end LowRank
