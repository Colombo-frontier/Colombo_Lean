import FullJet.OracleCandidate
import FullJet.BoundedOracleProgram
import FullJet.FiniteValidation

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n m B H : ℕ}

/-- Exact full-gradient validation costs n actual component queries. -/
noncomputable def validatePointProgram (hp : 1 ≤ p) (ε : ℝ) (x fallback : E) :
    OracleProgram (Fin n × E) (JetPacket p E) E := by
  classical
  exact (OracleProgram.collect n (fun i => (i, x))).bind fun replies =>
    .done (if ‖(n : ℝ)⁻¹ • ∑ i, packetGradient hp (replies i)‖ ≤ ε then x else fallback)

theorem validatePointProgram_uses (hp : 1 ≤ p) (ε : ℝ) (x fallback : E) :
    (validatePointProgram (n := n) hp ε x fallback).Uses n := by
  unfold validatePointProgram
  simpa only [Nat.add_zero] using OracleProgram.uses_bind
    (OracleProgram.collect_uses n _) _ (fun replies => OracleProgram.Uses.done _)

theorem eval_validatePointProgram {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (ε : ℝ) (x fallback : E) :
    (validatePointProgram hp ε x fallback).eval (fun q => fullJet p (f q.1) q.2) =
      if ‖fderiv ℝ (average f) x‖ ≤ ε then x else fallback := by
  classical
  simp only [validatePointProgram, OracleProgram.eval_bind, OracleProgram.eval_collect,
    OracleProgram.eval, snapshot_initial_gradient hf hp]

noncomputable def verifiedAttemptProgram (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) (fallback : E) : OracleProgram (Fin n × E) (JetPacket p E) E :=
  (candidateProgram hp M r hr seed).bind fun x => validatePointProgram hp ε x fallback

theorem verifiedAttemptProgram_within (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) (fallback : E) :
    (verifiedAttemptProgram hp M r ε hr seed fallback).Within (H * epochQueryCost n m B + n) :=
  OracleProgram.within_bind
    ((candidateProgram_uses hp M r hr seed).within.mono (candidateQueryCost_le n m B seed.2)) _
    (fun x => (validatePointProgram_uses hp ε x fallback).within)

/-- Execute independent attempts, preserving the last point that passed
exact validation. All attempted computations remain within a fixed budget. -/
noncomputable def verifiedRepeatProgram (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r) :
    (K : ℕ) → (Fin K → RandomEpochSeed H m B n) → OracleProgram (Fin n × E) (JetPacket p E) E
  | 0, _ => .done 0
  | K + 1, seeds => (verifiedRepeatProgram hp M r ε hr K (Fin.init seeds)).bind fun fallback =>
      verifiedAttemptProgram hp M r ε hr (seeds (Fin.last K)) fallback

theorem verifiedRepeatProgram_within (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r)
    (K : ℕ) (seeds : Fin K → RandomEpochSeed H m B n) :
    (verifiedRepeatProgram (E := E) hp M r ε hr K seeds).Within
      (K * (H * epochQueryCost n m B + n)) := by
  induction K with
  | zero => exact OracleProgram.Within.done _ _
  | succ K ih =>
    rw [Nat.add_mul, Nat.one_mul]
    exact OracleProgram.within_bind (ih (Fin.init seeds)) _
      (fun fallback => verifiedAttemptProgram_within hp M r ε hr _ fallback)

noncomputable def verifiedEpochOutput (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r ε : ℝ) (hr : 0 ≤ r) (K : ℕ) (seeds : Fin K → RandomEpochSeed H m B n) : E := by
  classical
  exact validatedChoice 0 (fun x => ‖fderiv ℝ (average f) x‖ ≤ ε)
    (multiEpochOutput hp f M r hr) K seeds

theorem eval_verifiedRepeatProgram {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r) (K : ℕ) (seeds : Fin K → RandomEpochSeed H m B n) :
    (verifiedRepeatProgram hp M r ε hr K seeds).eval (fun q => fullJet p (f q.1) q.2) =
      verifiedEpochOutput hp f M r ε hr K seeds := by
  classical
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [verifiedRepeatProgram, OracleProgram.eval_bind, ih, verifiedAttemptProgram,
      eval_candidateProgram, eval_validatePointProgram hf hp, verifiedEpochOutput, validatedChoice]

noncomputable def verifiedJetAlgorithm (hp : 1 ≤ p) (index : Fin n)
    (M r ε : ℝ) (hr : 0 ≤ r) (K : ℕ) : JetAlgorithm (Fin K → RandomEpochSeed H m B n) E n p :=
  programJetAlgorithm index (verifiedRepeatProgram hp M r ε hr K)

theorem verifiedJetAlgorithm_result {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (index : Fin n) (M r ε : ℝ) (hr : 0 ≤ r)
    (K : ℕ) (seeds : Fin K → RandomEpochSeed H m B n) :
    (verifiedJetAlgorithm hp index M r ε hr K).result
      (K * (H * epochQueryCost n m B + n)) f seeds = verifiedEpochOutput hp f M r ε hr K seeds := by
  rw [verifiedJetAlgorithm, programJetAlgorithm_result_within index _ _
    (verifiedRepeatProgram_within hp M r ε hr K)]
  exact eval_verifiedRepeatProgram hf hp M r ε hr K seeds

end FullJet
