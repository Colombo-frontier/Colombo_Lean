import FullJet.VerifiedOracle
import FullJet.PaddedOracleProgram

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n m B H : ℕ}

/-- Exact validation returns a successful point or an explicit failure flag. -/
noncomputable def certifyPointProgram (hp : 1 ≤ p) (ε : ℝ) (x : E) :
    OracleProgram (Fin n × E) (JetPacket p E) (Option E) := by
  classical
  exact (OracleProgram.collect n (fun i => (i, x))).bind fun replies =>
    .done (if ‖(n : ℝ)⁻¹ • ∑ i, packetGradient hp (replies i)‖ ≤ ε then some x else none)

theorem certifyPointProgram_uses (hp : 1 ≤ p) (ε : ℝ) (x : E) :
    (certifyPointProgram (n := n) hp ε x).Uses n := by
  unfold certifyPointProgram
  simpa only [Nat.add_zero] using OracleProgram.uses_bind
    (OracleProgram.collect_uses n _) _ (fun replies => OracleProgram.Uses.done _)

theorem eval_certifyPointProgram {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (ε : ℝ) (x : E) :
    (certifyPointProgram hp ε x).eval (fun q => fullJet p (f q.1) q.2) =
      if ‖fderiv ℝ (average f) x‖ ≤ ε then some x else none := by
  classical
  simp only [certifyPointProgram, OracleProgram.eval_bind, OracleProgram.eval_collect,
    OracleProgram.eval, snapshot_initial_gradient hf hp]

noncomputable def certifiedAttemptProgram (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) : OracleProgram (Fin n × E) (JetPacket p E) (Option E) :=
  (candidateProgram hp M r hr seed).bind fun x => certifyPointProgram hp ε x

theorem certifiedAttemptProgram_within (hp : 1 ≤ p) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) :
    (certifiedAttemptProgram (E := E) hp M r ε hr seed).Within (H * epochQueryCost n m B + n) :=
  OracleProgram.within_bind
    ((candidateProgram_uses hp M r hr seed).within.mono (candidateQueryCost_le n m B seed.2)) _
    (fun x => (certifyPointProgram_uses hp ε x).within)

/-- Paid padding gives each restart attempt a common strictly positive
length when n is positive, without changing its validated result. -/
noncomputable def certifiedTrialProgram (hp : 1 ≤ p) (index : Fin n) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) : OracleProgram (Fin n × E) (JetPacket p E) (Option E) :=
  OracleProgram.pad (index, 0) none (H * epochQueryCost n m B + n)
    (certifiedAttemptProgram hp M r ε hr seed)

theorem certifiedTrialProgram_uses (hp : 1 ≤ p) (index : Fin n) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) :
    (certifiedTrialProgram (E := E) hp index M r ε hr seed).Uses (H * epochQueryCost n m B + n) :=
  OracleProgram.pad_uses _ _ _ _

theorem eval_certifiedTrialProgram {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (hp : 1 ≤ p) (index : Fin n) (M r ε : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) :
    (certifiedTrialProgram hp index M r ε hr seed).eval (fun q => fullJet p (f q.1) q.2) =
      if ‖fderiv ℝ (average f) (multiEpochOutput hp f M r hr seed)‖ ≤ ε
      then some (multiEpochOutput hp f M r hr seed) else none := by
  classical
  rw [certifiedTrialProgram, OracleProgram.eval_pad _ _ _ (certifiedAttemptProgram_within hp M r ε hr seed)]
  simp only [certifiedAttemptProgram, OracleProgram.eval_bind, eval_candidateProgram,
    eval_certifyPointProgram hf hp]

end FullJet
