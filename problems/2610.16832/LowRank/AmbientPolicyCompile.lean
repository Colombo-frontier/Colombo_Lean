import LowRank.AmbientOraclePolicy
import LowRank.AmbientQueryReduction

/-! Measurably compile arbitrary ambient queries to unit directions, using
one query per original step. The zero-residual case uses a harmless query
whose reply receives coefficient zero in the original-record decoder. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

variable {S T E : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {d q r : ℕ}

def ambientPolicyDirection (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (v : MeasurableStateMap S (Fin d → ℝ)) (mem : MeasurableStateMap T S)
    (vis : MeasurableStateMap T (VisibleFactorData d q (r + 1))) :
    MeasurableStateMap (T × VisibleFactorData d q (r + 1)) (Fin (r + 1) → ℝ) :=
  ⟨fun p => reducedQueryDirection b (vis.1 p.1) (v.1 (mem.1 p.1)),
    measurable_reducedQueryDirection b _ _ (vis.2.comp measurable_fst)
      (v.2.comp (mem.2.comp measurable_fst))⟩

def advanceReducedVisible (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (v : MeasurableStateMap S (Fin d → ℝ)) (mem : MeasurableStateMap T S)
    (vis : MeasurableStateMap T (VisibleFactorData d q (r + 1))) :
    MeasurableStateMap (T × (Fin d → ℝ)) (VisibleFactorData d (q + 1) r) :=
  ⟨fun p => recoverVisibleFactorData b
      (reducedQueryDirection b (vis.1 p.1) (v.1 (mem.1 p.1))) (vis.1 p.1) p.2,
    measurable_recoverVisibleFactorData b _ _ _
      (measurable_reducedQueryDirection b _ _ (vis.2.comp measurable_fst)
        (v.2.comp (mem.2.comp measurable_fst)))
      (vis.2.comp measurable_fst) measurable_snd⟩

def advanceReducedMemory (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (v : MeasurableStateMap S (Fin d → ℝ)) (mem : MeasurableStateMap T S)
    (vis : MeasurableStateMap T (VisibleFactorData d q (r + 1))) :
    MeasurableStateMap (T × (Fin d → ℝ)) (S × (Fin d → ℝ)) :=
  ⟨fun p => (mem.1 p.1, decodeReducedQuery b (vis.1 p.1) (v.1 (mem.1 p.1)) p.2),
    (mem.2.comp measurable_fst).prodMk
      (measurable_decodeReducedQuery b _ _ _ (vis.2.comp measurable_fst)
        (v.2.comp (mem.2.comp measurable_fst)) measurable_snd)⟩

def reduceAmbientOracle (d r : ℕ) : (n q : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → AmbientOraclePolicy d n S →
    MeasurableStateMap T S → MeasurableStateMap T (VisibleFactorData d q (r + n)) →
    VisibleOraclePolicy d r n q T
  | 0, _, _, _, _, _, _, _, _ => PUnit.unit
  | n + 1, q, _, _, _, _, policy, mem, vis =>
      let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
      (ambientPolicyDirection b policy.1 mem vis,
        reduceAmbientOracle d r n (q + 1) policy.2
          (advanceReducedMemory b policy.1 mem vis) (advanceReducedVisible b policy.1 mem vis))

def readReducedHistory (d r : ℕ) : (n q : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → AmbientOraclePolicy d n S →
    MeasurableStateMap T S → MeasurableStateMap T (VisibleFactorData d q (r + n)) →
    OracleHistory d n T → OracleHistory d n S
  | 0, _, _, _, _, _, _, mem, _ => mem.1
  | n + 1, q, _, _, _, _, policy, mem, vis =>
      let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
      readReducedHistory d r n (q + 1) policy.2
        (advanceReducedMemory b policy.1 mem vis) (advanceReducedVisible b policy.1 mem vis)

theorem reduceAmbientOracle_unit (d r n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : AmbientOraclePolicy d n S)
    (mem : MeasurableStateMap T S) (vis : MeasurableStateMap T (VisibleFactorData d q (r + n))) :
    VisibleOraclePolicy.IsUnit d r n q (reduceAmbientOracle d r n q policy mem vis) := by
  induction n generalizing q S T with
  | zero => trivial
  | succ n ih => exact ⟨fun p => reducedQueryDirection_norm _ _ _, ih (q + 1) policy.2 _ _⟩

theorem measurable_readReducedHistory (d r n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : AmbientOraclePolicy d n S)
    (mem : MeasurableStateMap T S) (vis : MeasurableStateMap T (VisibleFactorData d q (r + n))) :
    Measurable (readReducedHistory d r n q policy mem vis) := by
  induction n generalizing q S T with
  | zero => exact mem.2
  | succ n ih => exact ih (q + 1) policy.2 _ _

end
end LowRank
