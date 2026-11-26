import LowRank.VisibleOraclePolicy

/-! Compile a policy with only observable inputs into the enlarged Gaussian
history. The decoder records actual ambient replies, while latent rows and
right gauges remain confined to the enlarged state. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

abbrev MeasurableStateMap (S T : Type*) [MeasurableSpace S] [MeasurableSpace T] :=
  {f : S → T // Measurable f}

def liftVisibleQuery {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] {d t q r s : ℕ}
    (u : MeasurableStateMap (T × VisibleFactorData d q r) (Fin r → ℝ))
    (st : MeasurableStateMap S (FactorData d t q r s)) (mem : MeasurableStateMap S T) :
    MeasurableStateMap S (Fin r → ℝ) :=
  ⟨fun x => u.1 (mem.1 x, visibleFactorData (st.1 x)),
    u.2.comp (mem.2.prodMk ((measurable_visibleFactorData d t q r s).comp st.2))⟩

def advanceFactorState {S E F : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : MeasurableStateMap S (Fin (r + 1) → ℝ))
    (st : MeasurableStateMap S (FactorData d t q (r + 1) (s + 1))) :
    MeasurableStateMap (S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) (FactorData d t (q + 1) r s) :=
  ⟨fun p => updateFactorData b c (u.1 p.1) (st.1 p.1) p.2,
    measurable_updateFactorData b c _ _ _ (u.2.comp measurable_fst)
      (st.2.comp measurable_fst) measurable_snd⟩

def advanceOracleMemory {S T E F : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : MeasurableStateMap S (Fin (r + 1) → ℝ))
    (st : MeasurableStateMap S (FactorData d t q (r + 1) (s + 1)))
    (mem : MeasurableStateMap S T) :
    MeasurableStateMap (S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) (T × (Fin d → ℝ)) :=
  ⟨fun p => (mem.1 p.1, decodeFactorReply b c (u.1 p.1) (visibleFactorData (st.1 p.1)) p.2),
    (mem.2.comp measurable_fst).prodMk (measurable_decodeFactorReply b c _ _ _
      (u.2.comp measurable_fst)
      ((measurable_visibleFactorData d t q (r + 1) (s + 1)).comp (st.2.comp measurable_fst))
      measurable_snd)⟩

def compileVisibleOracle (d t r s : ℕ) : (n q : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → VisibleOraclePolicy d r n q T →
    MeasurableStateMap S (FactorData d t q (r + n) (s + n)) → MeasurableStateMap S T →
    GaussianPolicy r s n S
  | 0, _, _, _, _, _, _, _, _ => PUnit.unit
  | n + 1, q, _, _, _, _, policy, st, mem =>
      let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
      let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
      let u := liftVisibleQuery policy.1 st mem
      (u, compileVisibleOracle d t r s n (q + 1) policy.2
        (advanceFactorState b c u st) (advanceOracleMemory b c u st mem))

def readOracleHistory (d t r s : ℕ) : (n q : ℕ) → {S T : Type u} →
    [MeasurableSpace S] → [MeasurableSpace T] → VisibleOraclePolicy d r n q T →
    MeasurableStateMap S (FactorData d t q (r + n) (s + n)) → MeasurableStateMap S T →
    GaussianHistory r s n S → OracleHistory d n T
  | 0, _, _, _, _, _, _, _, mem => mem.1
  | n + 1, q, _, _, _, _, policy, st, mem =>
      let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
      let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
      let u := liftVisibleQuery policy.1 st mem
      readOracleHistory d t r s n (q + 1) policy.2
        (advanceFactorState b c u st) (advanceOracleMemory b c u st mem)

theorem measurable_readOracleHistory (d t r s n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : VisibleOraclePolicy d r n q T)
    (st : MeasurableStateMap S (FactorData d t q (r + n) (s + n))) (mem : MeasurableStateMap S T) :
    Measurable (readOracleHistory d t r s n q policy st mem) := by
  induction n generalizing q S T with
  | zero => exact mem.2
  | succ n ih => exact ih (q + 1) policy.2 _ _

end
end LowRank
