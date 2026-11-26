import FullJet.OracleEpoch
import FullJet.RandomEpochOutput

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n m B H : ℕ}

/-- Complete successive epochs, taking each new snapshot at the preceding
actual endpoint. The program has no access to the component functions. -/
noncomputable def epochCenterProgram (hp : 1 ≤ p) (M r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    (e : ℕ) → (Fin e → Fin m → Fin B → Fin n) → OracleProgram (Fin n × E) (JetPacket p E) E
  | 0, _ => .done 0
  | e + 1, samples => (epochCenterProgram hp M r hr m e (Fin.init samples)).bind fun center =>
      (epochProgram hp center M r hr m (samples (Fin.last e))).bind fun state =>
        .done (center + state.offset)

theorem epochCenterProgram_uses (hp : 1 ≤ p) (M r : ℝ) (hr : 0 ≤ r) (m e : ℕ)
    (samples : Fin e → Fin m → Fin B → Fin n) :
    (epochCenterProgram (E := E) hp M r hr m e samples).Uses (e * epochQueryCost n m B) := by
  induction e with
  | zero =>
    simp only [Nat.zero_mul, epochCenterProgram]
    exact OracleProgram.Uses.done _
  | succ e ih =>
    rw [Nat.add_mul, Nat.one_mul]
    apply OracleProgram.uses_bind (ih (Fin.init samples)) _
    intro center
    simpa only [Nat.add_zero] using OracleProgram.uses_bind
      (epochProgram_uses hp center M r hr m _) _ (fun state => OracleProgram.Uses.done _)

theorem eval_epochCenterProgram (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (m e : ℕ) (samples : Fin e → Fin m → Fin B → Fin n) :
    (epochCenterProgram hp M r hr m e samples).eval (fun q => fullJet p (f q.1) q.2) =
      multiEpochCenter hp f M r hr m e samples := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simp only [epochCenterProgram, OracleProgram.eval_bind, ih, eval_epochProgram,
      OracleProgram.eval, multiEpochCenter, epochPathPoint_last]

/-- Compute the selected point by running precisely the required prefix of
the same trajectory. The independent index only determines where to stop;
the model updates before that point are unchanged. -/
noncomputable def candidateProgram (hp : 1 ≤ p) (M r : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) : OracleProgram (Fin n × E) (JetPacket p E) E :=
  (epochCenterProgram hp M r hr m seed.2.1.val
    (samplePrefix (Nat.le_of_lt seed.2.1.isLt) seed.1)).bind fun center =>
      (epochProgram hp center M r hr (seed.2.2.val + 1)
        (samplePrefix (Nat.succ_le_of_lt seed.2.2.isLt) (seed.1 seed.2.1))).bind fun state =>
          .done (center + state.offset)

def candidateQueryCost (n m B : ℕ) {H : ℕ} (index : Fin H × Fin m) : ℕ :=
  index.1.val * epochQueryCost n m B + epochQueryCost n (index.2.val + 1) B

theorem candidateProgram_uses (hp : 1 ≤ p) (M r : ℝ) (hr : 0 ≤ r)
    (seed : RandomEpochSeed H m B n) :
    (candidateProgram (E := E) hp M r hr seed).Uses (candidateQueryCost n m B seed.2) := by
  apply OracleProgram.uses_bind (epochCenterProgram_uses hp M r hr m _ _) _
  intro center
  simpa only [Nat.add_zero] using OracleProgram.uses_bind
    (epochProgram_uses hp center M r hr _ _) _ (fun state => OracleProgram.Uses.done _)

theorem candidateQueryCost_le (n m B : ℕ) {H : ℕ} (index : Fin H × Fin m) :
    candidateQueryCost n m B index ≤ H * epochQueryCost n m B := by
  have ht : epochQueryCost n (index.2.val + 1) B ≤ epochQueryCost n m B :=
    Nat.add_le_add_left (Nat.mul_le_mul_right (2 * B) (Nat.succ_le_of_lt index.2.isLt)) n
  calc
    candidateQueryCost n m B index ≤ (index.1.val + 1) * epochQueryCost n m B := by
      dsimp only [candidateQueryCost]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left ht _
    _ ≤ H * epochQueryCost n m B := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt index.1.isLt)

theorem eval_candidateProgram (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (seed : RandomEpochSeed H m B n) :
    (candidateProgram hp M r hr seed).eval (fun q => fullJet p (f q.1) q.2) =
      multiEpochOutput hp f M r hr seed := by
  simp only [candidateProgram, OracleProgram.eval_bind, eval_epochCenterProgram,
    eval_epochProgram, OracleProgram.eval]
  rfl

noncomputable def candidateJetAlgorithm (hp : 1 ≤ p) (index : Fin n)
    (M r : ℝ) (hr : 0 ≤ r) : JetAlgorithm (RandomEpochSeed H m B n) E n p :=
  programJetAlgorithm index (candidateProgram hp M r hr)

/-- The original oracle model, at an explicit fixed budget, produces exactly
the candidate whose finite probability law was analyzed. -/
theorem candidateJetAlgorithm_result (hp : 1 ≤ p) (index : Fin n)
    (M r : ℝ) (hr : 0 ≤ r) (f : Fin n → E → ℝ) (seed : RandomEpochSeed H m B n) :
    (candidateJetAlgorithm hp index M r hr).result (H * epochQueryCost n m B) f seed =
      multiEpochOutput hp f M r hr seed := by
  rw [candidateJetAlgorithm, programJetAlgorithm_result_at index _ f seed
    (candidateQueryCost n m B seed.2) _ (candidateProgram_uses hp M r hr seed)
    (candidateQueryCost_le n m B seed.2)]
  exact eval_candidateProgram hp f M r hr seed

end FullJet
