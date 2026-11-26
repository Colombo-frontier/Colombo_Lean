import Matvec.TwoSidedGaussianProcess
import Matvec.TwoSidedAmbientState

/-! Explicit compilation of arbitrary measurable ambient two-sided query
policies into the Gaussian extra-exposure process. -/

namespace Matvec
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix
noncomputable section
universe u

abbrev OracleMap (S T : Type*) [MeasurableSpace S] [MeasurableSpace T] :=
  {f : S → T // Measurable f}

abbrev AmbientQuery (m n : ℕ) := (Fin m → ℝ) × (Fin n → ℝ)

def TwoSidedOracleHistory (m n : ℕ) : ℕ → Type u → Type u
  | 0, S => S
  | t + 1, S => TwoSidedOracleHistory m n t (S × AmbientQuery m n)

instance twoSidedOracleHistoryMeasurable (m n t : ℕ) (S : Type u) [MeasurableSpace S] :
    MeasurableSpace (TwoSidedOracleHistory m n t S) := by
  induction t generalizing S with
  | zero => exact inferInstanceAs (MeasurableSpace S)
  | succ t ih => exact ih (S × AmbientQuery m n)

def TwoSidedOraclePolicy (m n : ℕ) : (t : ℕ) → (S : Type u) → [MeasurableSpace S] → Type u
  | 0, _, _ => PUnit
  | t + 1, S, _ => OracleMap S (AmbientQuery m n) ×
      TwoSidedOraclePolicy m n t (S × AmbientQuery m n)

def runTwoSidedOracle (m n : ℕ) : (t : ℕ) → {S : Type u} → [MeasurableSpace S] →
    TwoSidedOraclePolicy m n t S → Matrix (Fin m) (Fin n) ℝ → S →
    TwoSidedOracleHistory m n t S
  | 0, _, _, _, _, z => z
  | t + 1, _, _, p, A, z =>
      runTwoSidedOracle m n t p.2 A (z, (A *ᵥ (p.1.1 z).2, Aᵀ *ᵥ (p.1.1 z).1))

def residualLeft {m n r s : ℕ} {S : Type u} [MeasurableSpace S]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) : OracleMap S (Fin (r + 1) → ℝ) :=
  ⟨fun z => (st.1 z).2.1ᵀ *ᵥ (q.1 z).1, by
    have hst := st.2
    have hq := q.2
    apply measurable_pi_lambda; intro i
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    fun_prop⟩

def residualRight {m n r s : ℕ} {S : Type u} [MeasurableSpace S]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) : OracleMap S (Fin (s + 1) → ℝ) :=
  ⟨fun z => (st.1 z).2.2ᵀ *ᵥ (q.1 z).2, by
    have hst := st.2
    have hq := q.2
    apply measurable_pi_lambda; intro i
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    fun_prop⟩

def oracleLeftGauge {m n r s : ℕ} {S : Type u} [MeasurableSpace S]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) :
    OracleMap S (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :=
  ⟨fun z => queryGauge (EuclideanSpace.basisFun (Fin (r + 1)) ℝ) ((residualLeft st q).1 z),
    (measurable_queryGauge _).comp (residualLeft st q).2⟩

def oracleRightGauge {m n r s : ℕ} {S : Type u} [MeasurableSpace S]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) :
    OracleMap S (Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ) :=
  ⟨fun z => queryGauge (EuclideanSpace.basisFun (Fin (s + 1)) ℝ) ((residualRight st q).1 z),
    (measurable_queryGauge _).comp (residualRight st q).2⟩

def nextTwoSidedState {m n r s : ℕ} {S : Type u} [MeasurableSpace S]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) :
    OracleMap (S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) (TwoSidedState m n r s) :=
  ⟨fun p => updateTwoSidedState (st.1 p.1) ((oracleLeftGauge st q).1 p.1)
      ((oracleRightGauge st q).1 p.1) p.2,
    measurable_updateTwoSidedState.comp
      ((st.2.comp measurable_fst).prodMk
        ((((oracleLeftGauge st q).2.comp measurable_fst).prodMk
          ((oracleRightGauge st q).2.comp measurable_fst)).prodMk measurable_snd))⟩

def nextTwoSidedMemory {m n r s : ℕ} {S T : Type u} [MeasurableSpace S] [MeasurableSpace T]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) (mem : OracleMap S T) :
    OracleMap (S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) (T × AmbientQuery m n) :=
  ⟨fun p => (mem.1 p.1, ambientTwoSidedReply (st.1 p.1) (q.1 p.1).1 (q.1 p.1).2 p.2),
    (mem.2.comp measurable_fst).prodMk
      (measurable_ambientTwoSidedReply.comp
        (((st.2.comp measurable_fst).prodMk (q.2.comp measurable_fst)).prodMk measurable_snd))⟩

def compileTwoSidedOracle (m n r s : ℕ) : (t : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → TwoSidedOraclePolicy m n t T →
    OracleMap S (TwoSidedState m n (r + t) (s + t)) → OracleMap S T → TwoSidedPolicy r s t S
  | 0, _, _, _, _, _, _, _ => PUnit.unit
  | t + 1, _, _, _, _, policy, st, mem =>
      let q : OracleMap _ (AmbientQuery m n) := ⟨policy.1.1 ∘ mem.1, policy.1.2.comp mem.2⟩
      ((residualLeft st q, residualRight st q),
        compileTwoSidedOracle m n r s t policy.2 (nextTwoSidedState st q)
          (nextTwoSidedMemory st q mem))

/-- Replay the original history using only the enhanced coordinate record. -/
def decodeTwoSidedHistory (m n r s : ℕ) : (t : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → TwoSidedOraclePolicy m n t T →
    OracleMap S (TwoSidedState m n (r + t) (s + t)) → OracleMap S T →
    LowRank.GaussianHistory r s t S → TwoSidedOracleHistory m n t T
  | 0, _, _, _, _, _, _, mem => mem.1
  | t + 1, _, _, _, _, policy, st, mem =>
      let q : OracleMap _ (AmbientQuery m n) := ⟨policy.1.1 ∘ mem.1, policy.1.2.comp mem.2⟩
      decodeTwoSidedHistory m n r s t policy.2 (nextTwoSidedState st q) (nextTwoSidedMemory st q mem)

theorem measurable_decodeTwoSidedHistory (m n r s t : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : TwoSidedOraclePolicy m n t T)
    (st : OracleMap S (TwoSidedState m n (r + t) (s + t))) (mem : OracleMap S T) :
    Measurable (decodeTwoSidedHistory m n r s t policy st mem) := by
  induction t generalizing S T with
  | zero => exact mem.2
  | succ t ih => exact ih policy.2 _ _

theorem nextTwoSidedState_represents {m n r s : ℕ} {S : Type u} [MeasurableSpace S]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n))
    (p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    let step := twoSidedGaussianStep (oracleLeftGauge st q).1 (oracleRightGauge st q).1 p
    representedTwoSided ((nextTwoSidedState st q).1 step.1) step.2 =
      representedTwoSided (st.1 p.1) p.2 := by
  exact updateTwoSidedState_represents (st.1 p.1) _ _
    (LowRank.gaugeMatrix_transpose_mul_self _ _) (LowRank.gaugeMatrix_transpose_mul_self _ _) p.2

theorem nextTwoSidedMemory_reply {m n r s : ℕ} {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T]
    (st : OracleMap S (TwoSidedState m n (r + 1) (s + 1)))
    (q : OracleMap S (AmbientQuery m n)) (mem : OracleMap S T)
    (p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    let step := twoSidedGaussianStep (oracleLeftGauge st q).1 (oracleRightGauge st q).1 p
    (nextTwoSidedMemory st q mem).1 step.1 =
      (mem.1 p.1, (representedTwoSided (st.1 p.1) p.2 *ᵥ (q.1 p.1).2,
        (representedTwoSided (st.1 p.1) p.2)ᵀ *ᵥ (q.1 p.1).1)) := by
  exact congrArg (fun reply => (mem.1 p.1, reply))
    (ambientTwoSidedReply_eq_oracle (st.1 p.1) (q.1 p.1).1 (q.1 p.1).2 p.2)

/-- Pointwise replay for every ambient matrix and every seed. Zero/redundant
queries require no exceptional event and are included automatically. -/
theorem compileTwoSidedOracle_replay (m n r s t : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : TwoSidedOraclePolicy m n t T)
    (st : OracleMap S (TwoSidedState m n (r + t) (s + t))) (mem : OracleMap S T)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    decodeTwoSidedHistory m n r s t policy st mem
      (runTwoSidedPolicy r s t (compileTwoSidedOracle m n r s t policy st mem) p).1 =
      runTwoSidedOracle m n t policy (representedTwoSided (st.1 p.1) p.2) (mem.1 p.1) := by
  induction t generalizing S T with
  | zero => rfl
  | succ t ih =>
    let q : OracleMap S (AmbientQuery m n) := ⟨policy.1.1 ∘ mem.1, policy.1.2.comp mem.2⟩
    let step := twoSidedGaussianStep (oracleLeftGauge st q).1 (oracleRightGauge st q).1 p
    have h := ih policy.2 (nextTwoSidedState st q) (nextTwoSidedMemory st q mem) step
    rw [nextTwoSidedState_represents, nextTwoSidedMemory_reply] at h
    exact h

/-- The final affine state is itself read from the enhanced history. -/
def readTwoSidedState (m n r s : ℕ) : (t : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → TwoSidedOraclePolicy m n t T →
    OracleMap S (TwoSidedState m n (r + t) (s + t)) → OracleMap S T →
    LowRank.GaussianHistory r s t S → TwoSidedState m n r s
  | 0, _, _, _, _, _, st, _ => st.1
  | t + 1, _, _, _, _, policy, st, mem =>
      let q : OracleMap _ (AmbientQuery m n) := ⟨policy.1.1 ∘ mem.1, policy.1.2.comp mem.2⟩
      readTwoSidedState m n r s t policy.2 (nextTwoSidedState st q) (nextTwoSidedMemory st q mem)

theorem measurable_readTwoSidedState (m n r s t : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : TwoSidedOraclePolicy m n t T)
    (st : OracleMap S (TwoSidedState m n (r + t) (s + t))) (mem : OracleMap S T) :
    Measurable (readTwoSidedState m n r s t policy st mem) := by
  induction t generalizing S T with
  | zero => exact st.2
  | succ t ih => exact ih policy.2 _ _

theorem compileTwoSidedOracle_factorization (m n r s t : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : TwoSidedOraclePolicy m n t T)
    (st : OracleMap S (TwoSidedState m n (r + t) (s + t))) (mem : OracleMap S T)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    let out := runTwoSidedPolicy r s t (compileTwoSidedOracle m n r s t policy st mem) p
    representedTwoSided (readTwoSidedState m n r s t policy st mem out.1) out.2 =
      representedTwoSided (st.1 p.1) p.2 := by
  induction t generalizing S T with
  | zero => rfl
  | succ t ih =>
    let q : OracleMap S (AmbientQuery m n) := ⟨policy.1.1 ∘ mem.1, policy.1.2.comp mem.2⟩
    let step := twoSidedGaussianStep (oracleLeftGauge st q).1 (oracleRightGauge st q).1 p
    have h := ih policy.2 (nextTwoSidedState st q) (nextTwoSidedMemory st q mem) step
    rw [nextTwoSidedState_represents] at h
    exact h

theorem readTwoSidedState_orthogonal (m n r s t : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : TwoSidedOraclePolicy m n t T)
    (st : OracleMap S (TwoSidedState m n (r + t) (s + t))) (mem : OracleMap S T)
    (hst : ∀ z, (st.1 z).Orthogonal) :
    ∀ h, (readTwoSidedState m n r s t policy st mem h).Orthogonal := by
  induction t generalizing S T with
  | zero => exact hst
  | succ t ih =>
    apply ih policy.2
    intro p
    exact updateTwoSidedState_orthogonal (st.1 p.1) (hst p.1) _ _
      (queryGauge_orthogonal _ _) (queryGauge_orthogonal _ _) p.2

end
end Matvec
