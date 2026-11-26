import Matvec.MeasurableSimulation
import Matvec.TwoSidedAmbientPosterior

/-! Exact zero-overhead compilation of finite-array transcript policies into
the nested two-sided oracle policy used by the proved Gaussian posterior. -/
namespace Matvec
namespace MeasurableSimulation
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u v w

theorem measurable_prependHistory {R : Type v} {Seed : Type u}
    [MeasurableSpace R] [MeasurableSpace Seed] (j : ℕ) :
    Measurable (fun p : (Seed × R) × (Fin j → R) =>
      (p.1.1, (Fin.cons p.1.2 p.2 : Fin (j + 1) → R))) := by
  apply Measurable.prodMk measurable_fst.fst
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa only [Fin.cons_zero] using measurable_fst.snd
  · simpa only [Fin.cons_succ] using (measurable_pi_apply k).comp measurable_snd

def Policy.tail {Q : Type v} {R : Type v} {O : Type w} {Seed : Type u}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] [MeasurableSpace Seed]
    {T : ℕ} (alg : Policy Q R O (T + 1) Seed) : Policy Q R O T (Seed × R) where
  query j p h := alg.query (j + 1) p.1 (Fin.cons p.2 h)
  query_measurable j := (alg.query_measurable (j + 1)).comp (measurable_prependHistory j)
  output p h := alg.output p.1 (Fin.cons p.2 h)
  output_measurable := alg.output_measurable.comp (measurable_prependHistory T)

theorem Policy.tail_transcript {Q : Type v} {R : Type v} {O : Type w} {Seed : Type u}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] [MeasurableSpace Seed]
    {T : ℕ} (alg : Policy Q R O (T + 1) Seed) (oracle : Q → R) (seed : Seed) (j : ℕ) :
    let r := oracle (alg.query 0 seed Fin.elim0)
    Fin.cons r (alg.tail.transcript oracle (seed, r) j) = alg.transcript oracle seed (j + 1) := by
  dsimp only
  induction j with
  | zero =>
    ext i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) i
    change oracle (alg.query 0 seed Fin.elim0) =
      (Fin.snoc (α := fun _ => R) Fin.elim0
        (oracle (alg.query 0 seed Fin.elim0))) (Fin.last 0)
    rw [Fin.snoc_last]
  | succ j ih =>
    rw [Policy.transcript, Fin.cons_snoc_eq_snoc_cons]
    change Fin.snoc (α := fun _ => R)
      (Fin.cons (oracle (alg.query 0 seed Fin.elim0))
        (alg.tail.transcript oracle (seed, oracle (alg.query 0 seed Fin.elim0)) j))
      (oracle (alg.query (j + 1) seed
        (Fin.cons (oracle (alg.query 0 seed Fin.elim0))
          (alg.tail.transcript oracle (seed, oracle (alg.query 0 seed Fin.elim0)) j)))) = _
    rw [ih]
    rfl

theorem Policy.tail_run {Q : Type v} {R : Type v} {O : Type w} {Seed : Type u}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] [MeasurableSpace Seed]
    {T : ℕ} (alg : Policy Q R O (T + 1) Seed) (oracle : Q → R) (seed : Seed) :
    alg.tail.run oracle (seed, oracle (alg.query 0 seed Fin.elim0)) = alg.run oracle seed := by
  unfold Policy.run
  change alg.output seed (Fin.cons _ _) = _
  rw [alg.tail_transcript]

def Policy.toTwoSided {m n : ℕ} {O : Type w} [MeasurableSpace O] :
    (T : ℕ) → {Seed : Type u} → [MeasurableSpace Seed] →
    Policy (AmbientQuery m n) (AmbientQuery m n) O T Seed → TwoSidedOraclePolicy m n T Seed
  | 0, _, _, _ => PUnit.unit
  | T + 1, _, _, alg =>
      (⟨fun seed => alg.query 0 seed Fin.elim0,
        (alg.query_measurable 0).comp (measurable_id.prodMk measurable_const)⟩,
       alg.tail.toTwoSided T)

def Policy.nestedOutput {m n : ℕ} {O : Type w} [MeasurableSpace O] :
    (T : ℕ) → {Seed : Type u} → [MeasurableSpace Seed] →
    Policy (AmbientQuery m n) (AmbientQuery m n) O T Seed →
    TwoSidedOracleHistory m n T Seed → O
  | 0, _, _, alg => fun seed => alg.output seed Fin.elim0
  | T + 1, _, _, alg => alg.tail.nestedOutput T

theorem Policy.measurable_nestedOutput {m n : ℕ} {O : Type w} [MeasurableSpace O]
    (T : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery m n) (AmbientQuery m n) O T Seed) :
    Measurable (alg.nestedOutput T) := by
  induction T generalizing Seed with
  | zero => exact alg.output_measurable.comp (measurable_id.prodMk measurable_const)
  | succ T ih => exact ih alg.tail

theorem Policy.toTwoSided_replay {m n : ℕ} {O : Type w} [MeasurableSpace O]
    (T : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery m n) (AmbientQuery m n) O T Seed)
    (A : Matrix (Fin m) (Fin n) ℝ) (seed : Seed) :
    alg.nestedOutput T (runTwoSidedOracle m n T (alg.toTwoSided T) A seed) =
      alg.run (fun q => (A *ᵥ q.2, Aᵀ *ᵥ q.1)) seed := by
  induction T generalizing Seed with
  | zero => rfl
  | succ T ih =>
    change alg.tail.nestedOutput T (runTwoSidedOracle m n T (alg.tail.toTwoSided T) A
      (seed, (A *ᵥ (alg.query 0 seed Fin.elim0).2,
        Aᵀ *ᵥ (alg.query 0 seed Fin.elim0).1))) = _
    rw [ih]
    exact alg.tail_run _ seed

def Policy.enhancedOutput {O : Type w} [MeasurableSpace O]
    (r s T : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery (r + T) (s + T)) (AmbientQuery (r + T) (s + T)) O T Seed)
    (h : LowRank.GaussianHistory r s T Seed) : O :=
  alg.nestedOutput T (decodeAmbientTwoSided r s T (alg.toTwoSided T) h)

theorem Policy.measurable_enhancedOutput {O : Type w} [MeasurableSpace O]
    (r s T : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery (r + T) (s + T)) (AmbientQuery (r + T) (s + T)) O T Seed) :
    Measurable (alg.enhancedOutput r s T) :=
  (alg.measurable_nestedOutput T).comp
    (measurable_decodeTwoSidedHistory (r + T) (s + T) r s T (alg.toTwoSided T)
      (initialOracleState (r + T) (s + T) Seed) (initialOracleMemory Seed))

theorem Policy.enhancedOutput_replay {O : Type w} [MeasurableSpace O]
    (r s T : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery (r + T) (s + T)) (AmbientQuery (r + T) (s + T)) O T Seed)
    (p : Seed × Matrix (Fin (r + T)) (Fin (s + T)) ℝ) :
    alg.enhancedOutput r s T
      (runTwoSidedPolicy r s T (compiledAmbientPolicy r s T (alg.toTwoSided T)) p).1 =
      alg.run (fun q => (p.2 *ᵥ q.2, p.2ᵀ *ᵥ q.1)) p.1 := by
  unfold Policy.enhancedOutput
  rw [ambientTwoSided_replay]
  exact alg.toTwoSided_replay T p.2 p.1

theorem Policy.measurable_twoSided_run {O : Type w} [MeasurableSpace O]
    (r s T : ℕ) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery (r + T) (s + T)) (AmbientQuery (r + T) (s + T)) O T Seed) :
    Measurable (fun p : Seed × Matrix (Fin (r + T)) (Fin (s + T)) ℝ =>
      alg.run (fun q => (p.2 *ᵥ q.2, p.2ᵀ *ᵥ q.1)) p.1) := by
  have hp := runTwoSidedPolicy_preserving r s T (0 : Measure Seed)
    (compiledAmbientPolicy r s T (alg.toTwoSided T)) 1
  have h := (alg.measurable_enhancedOutput r s T).comp hp.measurable.fst
  change Measurable (fun p => alg.enhancedOutput r s T
    (runTwoSidedPolicy r s T (compiledAmbientPolicy r s T (alg.toTwoSided T)) p).1) at h
  simpa only [Policy.enhancedOutput_replay] using h

end
end MeasurableSimulation
end Matvec
