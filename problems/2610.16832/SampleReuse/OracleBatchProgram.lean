import SampleReuse.OracleChordProgram
import SecondOrder.ExactOracleProgram
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual persistent-oracle batches: the two endpoints of each chord use the
same immutable handle. The program reads only numerical replies and takes
exactly two calls per handle. This file is pathwise; independence is separate. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

/-- Universe-polymorphic form of the finite batch execution identity. -/
theorem persistentBatch_run {Q Y O : Type} {Z : Type*}
    (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O) :
    OracleProgram.run q₀ reply zs (OracleProgram.batch n qs finish) n =
      .done (finish (fun i => reply (qs i) (zs i))) := by
  induction n generalizing zs with
  | zero =>
    simp only [OracleProgram.run, OracleProgram.batch]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have hrequest (q : Q) (k : Y → OracleProgram Q Y O) (m : ℕ) :
        OracleProgram.run q₀ reply zs (.request q k) (m + 1) =
          OracleProgram.run q₀ reply (fun i => zs (i + 1)) (k (reply q (zs 0))) m := by
      induction m with
      | zero => rfl
      | succ m ihm => rw [OracleProgram.run, ihm, OracleProgram.run]
    rw [OracleProgram.batch, hrequest, ih]
    congr 2
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def chordBatchQueries {H d b : ℕ} (gradientRequest : Bool)
    (handles : Fin b → Fin H) (x y : Point d) (k : Fin (b * 2)) : PersistentQuery H d :=
  let ij := finProdFinEquiv.symm k
  (gradientRequest, handles ij.1, if ij.2 = 0 then x else y)

def gradientBatchFinish {d b : ℕ} (ys : Fin (b * 2) → PersistentReply d) : Point d :=
  (b : ℝ)⁻¹ • ∑ i : Fin b,
    ((ys (finProdFinEquiv (i, 0))).1 - (ys (finProdFinEquiv (i, 1))).1)

def hessianBatchFinish {d b : ℕ} (ys : Fin (b * 2) → PersistentReply d) :
    Point d →L[ℝ] Point d :=
  (b : ℝ)⁻¹ • ∑ i : Fin b,
    ((ys (finProdFinEquiv (i, 0))).2 - (ys (finProdFinEquiv (i, 1))).2)

def gradientBatchProgram {H d b : ℕ} (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) (Point d) :=
  OracleProgram.batch (b * 2) (chordBatchQueries true handles x y) gradientBatchFinish

def hessianBatchProgram {H d b : ℕ} (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) (Point d →L[ℝ] Point d) :=
  OracleProgram.batch (b * 2) (chordBatchQueries false handles x y) hessianBatchFinish

theorem gradientBatchProgram_exact_calls {H d b : ℕ}
    (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram.UsesExactly (2 * b) (gradientBatchProgram handles x y) := by
  simpa only [gradientBatchProgram, Nat.mul_comm] using
    OracleProgram.batch_usesExactly (b * 2) (chordBatchQueries true handles x y)
      gradientBatchFinish

theorem hessianBatchProgram_exact_calls {H d b : ℕ}
    (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram.UsesExactly (2 * b) (hessianBatchProgram handles x y) := by
  simpa only [hessianBatchProgram, Nat.mul_comm] using
    OracleProgram.batch_usesExactly (b * 2) (chordBatchQueries false handles x y)
      hessianBatchFinish

theorem gradientBatchProgram_run {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (gradientBatchProgram handles x y) (2 * b) =
        .done ((b : ℝ)⁻¹ • ∑ i : Fin b, gradientChordSample F (x, y) (tape (handles i))) := by
  rw [Nat.mul_comm 2 b, gradientBatchProgram, persistentBatch_run]
  simp [gradientBatchFinish, chordBatchQueries, gradientChordSample]

theorem hessianBatchProgram_run {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (hessianBatchProgram handles x y) (2 * b) =
        .done ((b : ℝ)⁻¹ • ∑ i : Fin b, hessianChordSample F (x, y) (tape (handles i))) := by
  rw [Nat.mul_comm 2 b, hessianBatchProgram, persistentBatch_run]
  simp [hessianBatchFinish, chordBatchQueries, hessianChordSample]

theorem gradientBatchProgram_compiled_output {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x y : Point d) :
    let P := OracleProgram.algorithm q₀ (0, 0) 0 (gradientBatchProgram handles x y)
    P.output (2 * b) (persistentRun P.toQueryPolicy F tape (2 * b)) =
      (b : ℝ)⁻¹ • ∑ i : Fin b, gradientChordSample F (x, y) (tape (handles i)) := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ (2 * b) = _
  rw [OracleProgram.algorithm_output, gradientBatchProgram_run]
  rfl

theorem hessianBatchProgram_compiled_output {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x y : Point d) :
    let P := OracleProgram.algorithm q₀ (0, 0) 0 (hessianBatchProgram handles x y)
    P.output (2 * b) (persistentRun P.toQueryPolicy F tape (2 * b)) =
      (b : ℝ)⁻¹ • ∑ i : Fin b, hessianChordSample F (x, y) (tape (handles i)) := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ (2 * b) = _
  rw [OracleProgram.algorithm_output, hessianBatchProgram_run]
  rfl

theorem chordBatchQueries_measurable {H d b : ℕ} (gradientRequest : Bool)
    (k : Fin (b * 2)) :
    Measurable (fun w : (Fin b → Fin H) × (Point d × Point d) =>
      chordBatchQueries gradientRequest w.1 w.2.1 w.2.2 k) := by
  unfold chordBatchQueries
  apply measurable_const.prodMk
  apply ((measurable_pi_apply _).comp measurable_fst).prodMk
  split_ifs <;> fun_prop

theorem gradientBatchFinish_measurable {d b : ℕ} :
    Measurable (@gradientBatchFinish d b) := by
  unfold gradientBatchFinish
  fun_prop

theorem hessianBatchFinish_measurable {d b : ℕ} :
    Measurable (@hessianBatchFinish d b) := by
  unfold hessianBatchFinish
  fun_prop

theorem gradientBatchProgram_measurableFamily {H d b : ℕ}
    (q₀ : PersistentQuery H d) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun w : (Fin b → Fin H) × (Point d × Point d) =>
        gradientBatchProgram w.1 w.2.1 w.2.2) :=
  OracleProgram.batch_measurable q₀ 0 (b * 2) _ _
    (chordBatchQueries_measurable true) (gradientBatchFinish_measurable.comp measurable_snd)

theorem hessianBatchProgram_measurableFamily {H d b : ℕ}
    (q₀ : PersistentQuery H d) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun w : (Fin b → Fin H) × (Point d × Point d) =>
        hessianBatchProgram w.1 w.2.1 w.2.2) :=
  OracleProgram.batch_measurable q₀ 0 (b * 2) _ _
    (chordBatchQueries_measurable false) (hessianBatchFinish_measurable.comp measurable_snd)

end
end SampleReuse
